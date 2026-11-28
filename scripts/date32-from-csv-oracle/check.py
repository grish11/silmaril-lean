"""Pin CPython CSV input and independently read Lean's Date32 IPC with PyArrow."""

import argparse
import csv
from datetime import date
import hashlib
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
TESTS = ROOT / "Silmaril/Formats/Arrow/DateStream/FromCsv/Tests.lean"
LABEL = "日付"


def csv_bytes(rows, quoting=csv.QUOTE_MINIMAL):
    output = io.StringIO(newline="")
    csv.writer(output, lineterminator="\r\n", quoting=quoting).writerows(rows)
    return output.getvalue().encode("utf-8")


def fingerprint(data):
    return {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}


def lean_bytes(data):
    return "[" + ", ".join(f"0x{value:02X}" for value in data) + "]"


def lean_slots(slots):
    return "[" + ", ".join("none" if day is None else f"some ({day})" for day in slots) + "]"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pyarrow-path", type=Path)
    parser.add_argument("--regenerate", action="store_true", help="Update the fixture fingerprints")
    args = parser.parse_args()
    if args.pyarrow_path:
        sys.path.insert(0, str(args.pyarrow_path.resolve()))
    import pyarrow as pa
    import pyarrow.compute as pc

    assert sys.implementation.name == "cpython" and sys.version_info[:3] == (3, 13, 5)
    assert pa.__version__ == "26.0.1"
    signed = [-719528, -719469, -25509, -1, None, 0, 11016, 2932896]
    date32 = pa.array(signed, type=pa.int32()).view(pa.date32())
    spellings = pc.strftime(date32, format="%Y-%m-%d").to_pylist()
    assert spellings == ["0000-01-01", "0000-02-29", "1900-02-28", "1969-12-31",
                         None, "1970-01-01", "2000-02-29", "9999-12-31"]
    for day, spelling in zip(signed, spellings, strict=True):
        if spelling is not None and not spelling.startswith("0000"):
            assert (date.fromisoformat(spelling) - date(1970, 1, 1)).days == day

    rows = [[LABEL]] + [["N" if spelling is None else "T" + spelling] for spelling in spellings]
    required = "date, jour"
    cases = {
        "nullable": (LABEL, True, signed, csv_bytes(rows)),
        "required": (required, False, [-1, 11016],
                     csv_bytes([[required], ["T1969-12-31"], ["T2000-02-29"]], csv.QUOTE_ALL)),
        "header_only": (LABEL, False, [], csv_bytes([[LABEL]])),
    }
    adjacent = pa.array([-719529, 2932897], type=pa.int32()).view(pa.date32())
    below, above = pc.strftime(adjacent, format="%Y-%m-%d").to_pylist()
    assert (below, above) == ("-0001-12-31", "10000-01-01")
    refusals = {
        "required_null": (csv_bytes([[LABEL], ["N"]]), False, "(.requiredNull 0 0)"),
        "non_leap_century": (csv_bytes([[LABEL], ["T1900-02-29"]]), True, "(.csv (.parseCell 0))"),
        "below_profile": (csv_bytes([[LABEL], ["T" + below]]), True, "(.csv (.parseCell 0))"),
        "above_profile": (csv_bytes([[LABEL], ["T" + above]]), True, "(.csv (.parseCell 0))"),
        "unterminated_quote": ((LABEL + '\r\n"T1969-12-31\r\n').encode(), True,
                               "(.csv .malformedWire)"),
    }
    pin = {
        "cpython": "3.13.5",
        "pyarrow": "26.0.1",
        "pyarrow_wheel_sha256": "f71221bbc7707e3fad920d0478db9350791d4714ec445299ee0d56559fbc156c",
        "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "cases": {},
        "refused_csv": {case: fingerprint(data) for case, (data, _, _) in refusals.items()},
    }
    with tempfile.TemporaryDirectory(prefix="date32-from-csv-") as temporary:
        folder = Path(temporary)
        harness = folder / "Readback.lean"
        commands = []
        for case, (name, nullable, expected, data) in cases.items():
            field = json.dumps(name, ensure_ascii=False)
            path = json.dumps(str(folder / (case + ".arrow")))
            commands.append(f"#eval emitFixture {lean_bytes(data)} {field} "
                            f"{str(nullable).lower()} {lean_slots(expected)} {path}")
        for data, nullable, cause in refusals.values():
            commands.append(f"#guard rejects {lean_bytes(data)} {str(nullable).lower()} (.csv {cause})")
        harness.write_text(TESTS.read_text(encoding="utf-8") + "\n" + "\n".join(commands) + "\n",
                           encoding="utf-8")
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", str(harness)], cwd=ROOT, check=True)
        for case, (name, nullable, expected, data) in cases.items():
            emitted = (folder / (case + ".arrow")).read_bytes()
            with pa.ipc.open_stream(emitted) as reader:
                assert reader.schema == pa.schema([pa.field(name, pa.date32(), nullable=nullable)])
                assert [batch.column(0).view(pa.int32()).to_pylist() for batch in reader] == [expected]
            pin["cases"][case] = {
                "name": name, "nullable": nullable, "signed_slots": expected,
                "cpython_csv": fingerprint(data), "lean_ipc": fingerprint(emitted),
            }
    manifest = HERE / "fixtures.json"
    if args.regenerate:
        manifest.write_text(json.dumps(pin, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    else:
        assert pin == json.loads(manifest.read_text(encoding="utf-8")), json.dumps(pin, indent=2)
    print(f"PASS {len(cases)} CPython CSV → Lean IPC → PyArrow cases and {len(refusals)} pinned refusals")


if __name__ == "__main__":
    main()
