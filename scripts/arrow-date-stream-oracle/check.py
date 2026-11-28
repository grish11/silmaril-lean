"""Compare full DATE IPC streams and typed rejection cases with pinned fixtures."""

import argparse
from datetime import date
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
LEAN_DRIVER = """\
module

meta import Silmaril.Formats.Arrow.DateStream.Defs
meta import Silmaril.Formats.Arrow.Stream.Defs

open Silmaril Silmaril.Formats.Arrow

private meta def agrees (actual expected : Except DateStream.Error DateStream.Stream) : Bool :=
  match actual, expected with
  | .ok value, .ok wanted => decide (value = wanted)
  | .error cause, .error wanted => decide (cause = wanted)
  | _, _ => false

private meta def legacyRejectsDate (input : KBytes) : Bool :=
  match readStream {} input with
  | .error (.unsupported (.fieldType 8)) => true
  | _ => false
"""


def require(condition, message):
    if not condition:
        raise SystemExit(message)


def ipc_stream(pa, schema, rows):
    output = pa.BufferOutputStream()
    with pa.ipc.new_stream(output, schema) as writer:
        for values in rows:
            writer.write_batch(pa.record_batch([pa.array(values, type=schema.field(0).type)], schema=schema))
    return output.getvalue().to_pybytes()


def bytes_term(data):
    return f"(KBytes.leaf {len(data)} {int.from_bytes(data, 'little')})"


def dates_term(values):
    return "[" + ", ".join(
        "none" if value is None else f"some ⟨{value.year}, {value.month}, {value.day}⟩"
        for value in values
    ) + "]"


def positive_fixtures(pa):
    rows = [[date(1969, 12, 31), None], [], [date(2000, 2, 29), date(1970, 1, 1)]]
    for name, unit, arrow_type, expected in (
        ("date32", "day", pa.date32(), rows),
        ("date64", "millisecond", pa.date64(), rows),
        ("schema_only", "day", pa.date32(), []),
    ):
        schema = pa.schema([pa.field("日", arrow_type)])
        data = ipc_stream(pa, schema, expected)
        reader = pa.ipc.open_stream(data)
        require(reader.schema == schema, f"{name}: schema differs")
        observed = [batch.column(0).to_pylist() for batch in reader]
        require(observed == expected, f"{name}: ordered batch observation differs")
        field = reader.schema.field(0)
        batches = "[" + ", ".join(map(dates_term, observed)) + "]"
        wanted = f'.ok ⟨⟨"{field.name}", {str(field.nullable).lower()}, .{unit}⟩, {batches}⟩'
        yield name, data, wanted


def message_ranges(pa, data):
    reader = pa.BufferReader(data)
    ranges = []
    while reader.tell() < len(data) - 8:
        start = reader.tell()
        message = pa.ipc.read_message(reader)
        body = message.body
        body_start = reader.tell() - (body.size if body is not None else 0)
        ranges.append((start, body_start, reader.tell()))
    require(reader.tell() == len(data) - 8 and data[-8:] == struct.pack("<II", 0xFFFFFFFF, 0),
            "expected a final modern EOS")
    return ranges


def negative_fixtures(pa, streams):
    data32 = streams["date32"]
    ranges = message_ranges(pa, data32)
    require(len(ranges) == 4, "expected schema and three record batches")
    schema_end = ranges[0][2]
    second_offset = ranges[2][0]
    last_end = ranges[3][2]
    yield "missing_eos", data32[:-8], ".error (.batch 3 (.envelope (.malformed .truncated)))"
    yield "trailing_bytes", data32 + bytes(1), ".error (.batch 3 .trailingBytes)"
    yield "truncated_body", data32[:last_end - 1], ".error (.batch 2 (.body (.malformed .truncated)))"
    repeated = data32[:second_offset] + data32[:schema_end] + data32[second_offset:]
    yield "repeated_schema", repeated, ".error (.batch 1 (.metadata (.unsupported (.fieldType 8))))"
    corrupted = bytearray(data32)
    struct.pack_into("<I", corrupted, second_offset + 8, 0)
    yield "corrupt_record", bytes(corrupted), ".error (.batch 1 (.metadata (.malformed .flatbuffer)))"
    primitive = ipc_stream(pa, pa.schema([pa.field("日", pa.int32())]), [])
    yield "primitive_schema", primitive, ".error (.fieldType .int32)"
    wrong_kind = data32[:second_offset] + primitive[:-8] + data32[second_offset:]
    yield "primitive_schema_in_suffix", wrong_kind, ".error (.batch 1 .expectedRecordBatch)"
    data64 = streams["date64"]
    remainder = bytearray(data64)
    _, body_start, _ = message_ranges(pa, data64)[3]
    whole_day = 11016 * 86400000
    require(struct.unpack_from("<q", remainder, body_start) == (whole_day,), "expected leap-day value")
    struct.pack_into("<q", remainder, body_start, whole_day + 1)
    yield "date64_remainder", bytes(remainder), ".error (.batch 2 (.values (.nonWholeDay 0)))"


def fixtures(pa):
    positive = list(positive_fixtures(pa))
    yield from positive
    yield from negative_fixtures(pa, {name: data for name, data, _ in positive})


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--pyarrow-path", type=Path, help="Directory containing the pinned PyArrow wheel")
    args = parser.parse_args()
    if args.pyarrow_path is not None:
        sys.path.insert(0, str(args.pyarrow_path.resolve()))

    import pyarrow as pa

    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    require(platform.python_implementation() == "CPython" and platform.python_version() == manifest["cpython"],
            "Use the pinned CPython version")
    require(pa.__version__ == manifest["pyarrow"], "Use the pinned PyArrow version")
    commands = [LEAN_DRIVER]
    by_name = {}
    for name, data, expected in fixtures(pa):
        pin = {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}
        require(pin == manifest["streams"][name], f"{name}: pinned bytes differ")
        wire = bytes_term(data)
        by_name[name] = wire
        commands.append(f"#guard agrees (DateStream.read {{}} {wire}) ({expected})")
        print(f"{name} {pin['sha256']}", flush=True)
    commands.append(
        f"#guard agrees (DateStream.read {{ batches := 1 }} {by_name['date32']}) (.error (.batch 1 .batchLimit))"
    )
    commands.append(f"#guard legacyRejectsDate {by_name['date32']}")
    with tempfile.TemporaryDirectory(prefix="silmaril-arrow-date-stream-") as scratch:
        driver = Path(scratch) / "Fixtures.lean"
        driver.write_text("\n".join(commands) + "\n", encoding="utf-8")
        subprocess.run(
            [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", driver],
            cwd=ROOT,
            check=True,
        )
    print(f"PASS {len(commands) - 1} ordered DATE stream, stage error, and legacy profile checks")


if __name__ == "__main__":
    main()
