"""Produce Arrow TIMESTAMP fixtures with PyArrow and check the Lean CSV export."""

import argparse
import csv
import hashlib
import json
import os
from io import StringIO
from pathlib import Path
import platform
from runpy import run_path
import subprocess

import pyarrow as pa


ROOT = Path(__file__).resolve().parents[2]
WIRE = run_path(str(ROOT / "tests/formats/arrow-timestamp-stream/check-fixtures.py"))
EXPECTED_WIRE_SHA256 = "184517a1864dba4e745959b99dd095945025414c9c32a0848fea58423b9f6c6f"
GOOD = ("local_seconds", "zoned_millis", "offset_micros", "zoned_nanos", "schema_only", "empty_timezone")


def invoke(source, *args):
    subprocess.run([
        os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
        "--run", str(Path(__file__).with_name("Read.lean")), str(source), *map(str, args),
    ], cwd=ROOT, check=True)


def check_export(directory, name, source, wire):
    output = directory / f"{name}.csv"
    metadata = directory / f"{name}.json"
    with pa.ipc.open_stream(wire) as stream:
        [field] = stream.schema
        batches = [batch.column(0).cast(pa.int64()).to_pylist() for batch in stream]
    zone = field.type.tz
    if name == "empty_timezone":
        # PyArrow normalizes the empty string. The pinned fixture stores one explicitly.
        assert zone is None
        zone = ""
    expected_schema = {
        "name": field.name, "unit": field.type.unit, "timezone": zone, "nullable": field.nullable, "utc": bool(zone),
    }
    expected_rows = [[field.name]] + [["N" if tick is None else f"T{tick}"] for batch in batches for tick in batch]
    invoke(source, output, metadata)
    assert json.loads(metadata.read_text(encoding="utf-8")) == expected_schema, name
    with output.open(encoding="utf-8", newline="") as csv_file:
        assert list(csv.reader(csv_file)) == expected_rows, name
    canonical = StringIO(newline="")
    csv.writer(canonical, quoting=csv.QUOTE_ALL, lineterminator="\r\n").writerows(expected_rows)
    assert output.read_bytes() == canonical.getvalue().encode("utf-8"), name
    print(f"{name}: batches {list(map(len, batches))}, {field.type.unit}, zone {zone!r}, {len(expected_rows) - 1} rows")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", required=True, type=Path)
    output = parser.parse_args().out.resolve()
    output.mkdir(parents=True, exist_ok=True)
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1"
    digest = hashlib.sha256()
    fixtures = {}
    for name, wire, _ in WIRE["fixtures"]():
        digest.update(len(wire).to_bytes(8, "little"))
        digest.update(wire)
        fixtures[name] = wire
    assert digest.hexdigest() == EXPECTED_WIRE_SHA256
    for name in GOOD:
        source = output / f"{name}.arrows"
        source.write_bytes(fixtures[name])
        check_export(output, name, source, fixtures[name])

    header_wire = WIRE["write_stream"](pa.schema([pa.field("time\tbad", pa.timestamp("ns"))]))
    bad_inputs = {
        "missing-eos": fixtures["missing_eos"],
        "late-body": fixtures["truncated_body"],
        "occupied": fixtures["missing_eos"],
        "ipc-cap": fixtures["zoned_nanos"],
        "row-cap": fixtures["zoned_nanos"],
        "byte-cap": fixtures["zoned_nanos"],
        "header": header_wire,
    }
    for reason, wire in bad_inputs.items():
        source = output / f"{reason}.arrows"
        source.write_bytes(wire)
        invoke(source, reason)

    print(f"PyArrow {pa.__version__}: {len(GOOD)} exact named/CSV exports and {len(bad_inputs)} typed failures")
    print(f"Length-framed producer fixture SHA-256 {digest.hexdigest()}")


if __name__ == "__main__":
    main()
