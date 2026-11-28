"""Check scalar date adapters against pinned CPython and PyArrow observations."""

import argparse
from datetime import date, timedelta
import hashlib
import json
import os
from pathlib import Path
import platform
import struct
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[2]
MANIFEST = Path(__file__).with_name("fixtures.json")
EPOCH = date(1970, 1, 1)
DAYS_PER_CYCLE = 146097
MILLISECONDS_PER_DAY = 86400000

LEAN_PREAMBLE = """\
module

meta import Silmaril.Formats.DateInterop.Defs

open Silmaril.Formats.DateInterop
"""


def require(condition, message):
    if not condition:
        raise SystemExit(message)


def reference_civil(day):
    # Keep datetime inside a supported 400-year window, even at signed endpoints.
    cycles, remainder = divmod(day, DAYS_PER_CYCLE)
    civil = EPOCH + timedelta(days=remainder)
    return [civil.year + 400 * cycles, civil.month, civil.day]


def reference_day(civil):
    year, month, day = civil
    cycles, year_offset = divmod(year - EPOCH.year, 400)
    within = date(EPOCH.year + year_offset, month, day)
    return cycles * DAYS_PER_CYCLE + (within - EPOCH).days


def checked_signed(value, code):
    try:
        struct.pack(f"<{code}", value)
    except struct.error:
        return None
    return value


def column_array(pa, payloads, word_type, date_type):
    column = pa.array(payloads, type=word_type).view(date_type)
    column.validate(full=True)
    return column


def arrow_stream(pa, values, word_type, date_type):
    column = column_array(pa, values, word_type, date_type)
    table = pa.table({"date": column})
    sink = pa.BufferOutputStream()
    with pa.ipc.new_stream(sink, table.schema) as writer:
        writer.write_table(table)
    wire = sink.getvalue()
    parsed = pa.ipc.open_stream(wire).read_all()["date"].combine_chunks()
    require(parsed.type == date_type, "Arrow stream lost the date type")
    require(parsed.view(word_type).to_pylist() == values, "Arrow stream changed signed payloads")
    return wire.to_pybytes()


def parquet_file(pa, pq, values):
    column = column_array(pa, values, pa.int32(), pa.date32())
    sink = pa.BufferOutputStream()
    pq.write_table(pa.table({"date": column}), sink, version="2.6", data_page_version="1.0",
                   compression="NONE", use_dictionary=False, write_statistics=False)
    wire = sink.getvalue()
    parsed = pq.ParquetFile(wire)
    metadata = parsed.schema.column(0)
    require(metadata.physical_type == "INT32" and metadata.logical_type.type == "DATE",
            "Parquet column lacks the INT32 DATE annotation")
    observed = parsed.read()["date"].combine_chunks()
    require(observed.type == pa.date32() and observed.view(pa.int32()).to_pylist() == values,
            "Parquet changed signed DATE payloads")
    return wire.to_pybytes()


def oracle_outputs(pa, pq, fixtures):
    date32 = [case["date32"] for case in fixtures if case["date32"] is not None]
    date64 = [case["date64"] for case in fixtures if case["date64"] is not None]
    return {
        "arrow_date32_ipc": arrow_stream(pa, date32, pa.int32(), pa.date32()),
        "arrow_date64_ipc": arrow_stream(pa, date64, pa.int64(), pa.date64()),
        "parquet_date": parquet_file(pa, pq, date32),
    }


def lean_civil(civil):
    return "⟨" + ", ".join(map(str, civil)) + "⟩"


def lean_option(value):
    return "none" if value is None else f"some ({value})"


def lean_date_checks(case):
    day = case["epoch_day"]
    civil = lean_civil(case["civil"])
    date32, date64 = case["date32"], case["date64"]
    for namespace in ("Date32", "ParquetDate"):
        expected = lean_option(date32)
        yield f"#guard ({namespace}.ofEpochDay? ({day})).map Int32.toInt = {expected}"
        yield f"#guard ({namespace}.ofCivil? {civil}).map Int32.toInt = {expected}"
        if date32 is not None:
            yield f"#guard {namespace}.toEpochDay ({date32}) = ({day})"
            yield f"#guard {namespace}.toCivil ({date32}) = {civil}"
    expected = lean_option(date64)
    yield f"#guard (Date64.ofEpochDay? ({day})).map Int64.toInt = {expected}"
    yield f"#guard (Date64.ofCivil? {civil}).map Int64.toInt = {expected}"
    if date64 is not None:
        yield f"#guard Date64.toEpochDay? ({date64}) = some ({day})"
        yield f"#guard Date64.toCivil? ({date64}) = some {civil}"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--pyarrow-path", type=Path, help="Directory containing the pinned PyArrow wheel contents")
    args = parser.parse_args()
    if args.pyarrow_path is not None:
        sys.path.insert(0, str(args.pyarrow_path.resolve()))

    import pyarrow as pa
    import pyarrow.parquet as pq

    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    require(platform.python_implementation() == "CPython" and
            platform.python_version() == manifest["oracle"]["cpython"]["version"],
            "Use the pinned CPython version")
    require(pa.__version__ == manifest["oracle"]["pyarrow"]["version"], "Use the pinned PyArrow version")

    commands = [LEAN_PREAMBLE]
    for case in manifest["dates"]:
        day = case["epoch_day"]
        require(reference_civil(day) == case["civil"] and reference_day(case["civil"]) == day,
                f"{case['name']}: CPython Gregorian observation mismatch")
        require(checked_signed(day, "i") == case["date32"], f"{case['name']}: signed Int32 bounds mismatch")
        require(checked_signed(day * MILLISECONDS_PER_DAY, "q") == case["date64"],
                f"{case['name']}: signed Int64 bounds mismatch")
        if 1 <= case["civil"][0] <= 9999:
            civil = date(*case["civil"])
            for date_type, word_type, expected in (
                (pa.date32(), pa.int32(), case["date32"]),
                (pa.date64(), pa.int64(), case["date64"]),
            ):
                column = pa.array([civil], type=date_type)
                require(column.view(word_type).to_pylist() == [expected] and column.to_pylist() == [civil],
                        f"{case['name']}: PyArrow civil conversion mismatch for {date_type}")
        commands.extend(lean_date_checks(case))

    for payload in manifest["invalid_date64"]:
        column = pa.array([payload], type=pa.int64()).view(pa.date64())
        try:
            column.validate(full=True)
        except pa.ArrowInvalid as error:
            require("whole number of days" in str(error), f"Unexpected PyArrow error for {payload}")
        else:
            raise SystemExit(f"PyArrow accepted fractional Date64 payload {payload}")
        commands.append(f"#guard Date64.toEpochDay? ({payload}) = none")
        commands.append(f"#guard Date64.toCivil? ({payload}) = none")

    for civil in manifest["invalid_civil"]:
        try:
            reference_day(civil)
        except ValueError:
            pass
        else:
            raise SystemExit(f"CPython accepted invalid date {civil}")
        for namespace in ("Date32", "Date64", "ParquetDate"):
            commands.append(f"#guard {namespace}.ofCivil? {lean_civil(civil)} = none")

    outputs = oracle_outputs(pa, pq, manifest["dates"])
    for name, wire in outputs.items():
        expected = manifest["artifacts"][name]
        digest = hashlib.sha256(wire).hexdigest()
        require(len(wire) == expected["bytes"] and digest == expected["sha256"], f"{name}: fixture hash mismatch")
        print(f"PASS {name} {len(wire)} bytes {digest}", flush=True)

    with tempfile.TemporaryDirectory(prefix="silmaril-date-interop-") as scratch:
        driver = Path(scratch) / "Fixtures.lean"
        driver.write_text("\n".join(commands) + "\n", encoding="utf-8")
        subprocess.run(
            [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", driver],
            cwd=ROOT,
            check=True,
        )
    print(f"PASS {len(commands) - 1} Lean comparisons against pinned date fixtures")


if __name__ == "__main__":
    main()
