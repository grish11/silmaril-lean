"""Compare the typed Date32 CSV codec with pinned PyArrow and CPython fixtures."""

import argparse
import csv
from datetime import date
import hashlib
import io
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import tempfile


HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
TESTS = REPO / "Silmaril/Formats/Csv/Typed/Codecs/Date32/Tests.lean"
LABEL = "日付"
SLOTS = [-719528, -719469, -25509, -25508, -1, None, 0, 11016, 2932896]
TEXT = ["0000-01-01", "0000-02-29", "1900-02-28", "1900-03-01", "1969-12-31",
        None, "1970-01-01", "2000-02-29", "9999-12-31"]
ADJACENT = [-719529, 2932897]
ADJACENT_TEXT = ["-0001-12-31", "10000-01-01"]
NEGATIVE = {
    "century": ("T1900-02-29", "(.csv (.parseCell 0))"),
    "trailing bytes": ("T1970-01-01x", "(.csv (.parseCell 0))"),
    "empty present": ("T", "(.csv (.parseCell 0))"),
    "above maximum": ("T10000-01-01", "(.csv (.parseCell 0))"),
    "below minimum": ("T-0001-12-31", "(.csv (.parseCell 0))"),
    "quoted comma inside date": ("T1970-01-01,", "(.csv (.parseCell 0))"),
    "required null": ("N", "(.requiredNull 0 0)"),
}


def csv_wire(rows, quoting=csv.QUOTE_MINIMAL):
    output = io.StringIO(newline="")
    csv.writer(output, lineterminator="\r\n", quoting=quoting).writerows(rows)
    wire = output.getvalue().encode("utf-8")
    assert csv_rows(wire) == rows
    return wire


def csv_rows(wire):
    with io.StringIO(wire.decode("utf-8"), newline="") as stream:
        return list(csv.reader(stream, strict=True))


def metadata(wire):
    return {"bytes": len(wire), "sha256": hashlib.sha256(wire).hexdigest()}


def lean_bytes(wire):
    return "[" + ", ".join(f"0x{value:02X}" for value in wire) + "]"


def lean_slots(slots):
    return "[" + ", ".join("none" if day is None else f"some ({day})" for day in slots) + "]"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pyarrow-path", type=Path, help="Directory containing unpacked PyArrow")
    args = parser.parse_args()
    if args.pyarrow_path:
        sys.path.insert(0, str(args.pyarrow_path.resolve()))
    import pyarrow as pa
    import pyarrow.compute as pc
    import pyarrow.parquet as pq

    pin = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    assert platform.python_implementation() == "CPython"
    assert platform.python_version() == pin["cpython"]
    assert pa.__version__ == pin["pyarrow"]

    date32 = pa.array(SLOTS, type=pa.int32()).view(pa.date32())
    spellings = pc.strftime(date32, format="%Y-%m-%d").to_pylist()
    assert spellings == TEXT
    adjacent = pa.array(ADJACENT, type=pa.int32()).view(pa.date32())
    assert pc.strftime(adjacent, format="%Y-%m-%d").to_pylist() == ADJACENT_TEXT
    # CPython supplies a second date oracle for years 0001–9999.
    for day, spelling in zip(SLOTS, spellings, strict=True):
        if spelling is None:
            continue
        try:
            civil = date.fromisoformat(spelling)
        except ValueError:
            assert spelling in ("0000-01-01", "0000-02-29")
        else:
            assert not spelling.startswith("0000")
            assert civil.isoformat() == spelling
            assert (civil - date(1970, 1, 1)).days == day

    rows = [[LABEL]] + [["N" if value is None else "T" + value] for value in spellings]
    quoted_wire = csv_wire(rows, csv.QUOTE_ALL)
    minimal_wire = csv_wire(rows)
    schema = pa.schema([pa.field(LABEL, pa.date32(), nullable=True)])
    sink = pa.BufferOutputStream()
    pq.write_table(pa.Table.from_arrays([date32], schema=schema), sink, row_group_size=5,
                   version="2.6", data_page_version="1.0", compression="NONE",
                   use_dictionary=False, write_statistics=False, store_schema=False)
    parquet = sink.getvalue().to_pybytes()
    opened = pq.ParquetFile(pa.BufferReader(parquet))
    assert opened.schema_arrow == schema
    assert opened.num_row_groups == 2
    for index, expected in enumerate((SLOTS[:5], SLOTS[5:])):
        column = opened.read_row_group(index).column(0).combine_chunks()
        assert column.type == pa.date32() and column.view(pa.int32()).to_pylist() == expected

    negatives = {name: (csv_wire([[LABEL], [cell]]), cause)
                 for name, (cell, cause) in NEGATIVE.items()}
    malformed = (LABEL + '\r\n"T1970-01-01\r\n').encode()
    try:
        csv_rows(malformed)
    except csv.Error:
        pass
    else:
        raise AssertionError("CPython strict CSV accepted an unterminated quote")
    negatives["unterminated quote"] = (malformed, "(.csv .malformedWire)")
    actual = {
        "signed_slots": SLOTS,
        "spellings": spellings,
        "adjacent_signed_slots": ADJACENT,
        "adjacent_spellings": ADJACENT_TEXT,
        "csv_quote_all": metadata(quoted_wire),
        "csv_quote_minimal": metadata(minimal_wire),
        "parquet": metadata(parquet),
        "negative_csv": {name: metadata(value) for name, (value, _) in negatives.items()},
    }
    assert actual == pin["fixtures"], json.dumps(actual, indent=2)
    guards = [f"#guard checksCollected (Bytes.ofList {lean_bytes(parquet)}) "
              f"{lean_bytes(quoted_wire)} {lean_bytes(minimal_wire)} {lean_slots(SLOTS)}"]
    for day, spelling in zip(SLOTS, spellings, strict=True):
        if day is not None:
            guards.append(f"#guard checksCell ({day}) \"{spelling}\"")
    for name, (value, cause) in negatives.items():
        nullable = "false" if name == "required null" else "true"
        guards.append(f"#guard rejectsWire {lean_bytes(value)} {nullable} {cause}")
    with tempfile.TemporaryDirectory(prefix="date32-csv-") as directory:
        harness = Path(directory) / "Oracle.lean"
        harness.write_text(TESTS.read_text(encoding="utf-8") + "\n" + "\n".join(guards) + "\n",
                           encoding="utf-8")
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", str(harness)], cwd=REPO, check=True)
    print(f"PASS {len(SLOTS)} Date32 slots in two Parquet groups, {len(quoted_wire)} exact CSV bytes, "
          f"and {len(negatives)} pinned negative CSV fixtures")


if __name__ == "__main__":
    main()
