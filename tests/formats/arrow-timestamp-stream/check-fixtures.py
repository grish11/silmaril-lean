"""Check bounded TIMESTAMP IPC streams using pinned PyArrow producer bytes."""

import hashlib
import json
import os
from pathlib import Path
import platform
from runpy import run_path
import struct
import subprocess
import tempfile

import pyarrow as pa


ROOT = Path(__file__).resolve().parents[3]
DATE_STREAM = run_path(str(ROOT / "scripts/arrow-date-stream-oracle/check.py"))
FLATBUFFERS = run_path(str(ROOT / "scripts/arrow-date-schema-oracle/check.py"))
FIXTURE_SHA256 = "184517a1864dba4e745959b99dd095945025414c9c32a0848fea58423b9f6c6f"
UNITS = {"s": ("second", 1_000_000_000), "ms": ("millisecond", 1_000_000),
         "us": ("microsecond", 1_000), "ns": ("nanosecond", 1)}
ROWS = [[-(2**63), None, -2001], [], [0, None, 2**63 - 1]]


def write_stream(schema, columns=()):
    output = pa.BufferOutputStream()
    with pa.ipc.new_stream(output, schema) as writer:
        for column in columns:
            writer.write_batch(pa.RecordBatch.from_arrays([column], schema=schema))
    return output.getvalue().to_pybytes()


def timestamp_stream(unit, timezone, rows, nullable=True):
    timestamp = pa.timestamp(unit, timezone)
    schema = pa.schema([pa.field("time", timestamp, nullable=nullable)])
    columns = [pa.array(batch, type=pa.int64()).cast(timestamp) for batch in rows]
    wire = write_stream(schema, columns)
    reader = pa.ipc.open_stream(wire)
    assert reader.schema == schema
    assert [batch.column(0).cast(pa.int64()).to_pylist() for batch in reader] == rows
    return wire


def explicit_empty_timezone(wire):
    _, schema_end, _ = DATE_STREAM["message_ranges"](pa, wire)[0]
    schema = bytearray(wire[8:schema_end])
    field = FLATBUFFERS["field_table"](schema, 0)
    payload = FLATBUFFERS["target"](schema, FLATBUFFERS["slot"](schema, field, 3))
    string = FLATBUFFERS["target"](schema, FLATBUFFERS["slot"](schema, payload, 1))
    struct.pack_into("<I", schema, string, 0)
    schema[string + 4] = 0
    return wire[:8] + schema + wire[schema_end:]


def observation(wire, unit, timezone, rows, nullable=True):
    wire_term = DATE_STREAM["bytes_term"](wire)
    zone = "none" if timezone is None else f"(some {json.dumps(timezone)})"
    kind, scale = UNITS[unit]
    batches = "[" + ", ".join(
        "[" + ", ".join("none" if tick is None else f"some ({tick})" for tick in batch) + "]"
        for batch in rows
    ) + "]"
    return (f"#guard observes {{ batches := {len(rows)} }} {wire_term} "
            f".{kind} {zone} {str(bool(timezone)).lower()} {str(nullable).lower()} {scale} {batches}")


def rejection(wire, reason, limits="{}"):
    return f"#guard rejects {limits} {DATE_STREAM['bytes_term'](wire)} ({reason})"


def fixtures():
    canonical = timestamp_stream("ns", "Asia/Kathmandu", ROWS)
    for label, unit, timezone, wire, rows, nullable in (
        ("local_seconds", "s", None, timestamp_stream("s", None, ROWS), ROWS, True),
        ("zoned_millis", "ms", "UTC", timestamp_stream("ms", "UTC", ROWS), ROWS, True),
        ("offset_micros", "us", "+05:45", timestamp_stream("us", "+05:45", [[-1], []], False),
         [[-1], []], False),
        ("zoned_nanos", "ns", "Asia/Kathmandu", canonical, ROWS, True),
        ("schema_only", "ns", None, timestamp_stream("ns", None, []), [], True),
        ("empty_timezone", "ns", "", explicit_empty_timezone(canonical), ROWS, True),
    ):
        yield label, wire, observation(wire, unit, timezone, rows, nullable)

    ranges = DATE_STREAM["message_ranges"](pa, canonical)
    assert len(ranges) == 4
    second_start, second_body, _ = ranges[2]
    _, _, last_end = ranges[3]
    corrupt = bytearray(canonical)
    struct.pack_into("<I", corrupt, second_start + 8, 0)
    bad_bitmap = bytearray(canonical)
    bad_bitmap[ranges[1][1]] = 0xFF
    primitive = write_stream(pa.schema([pa.field("time", pa.int32())]))
    for label, wire, reason, limits in (
        ("missing_eos", canonical[:-8], ".batch 3 (.envelope (.malformed .truncated))", "{}"),
        ("trailing_bytes", canonical + b"\x00", ".batch 3 .trailingBytes", "{}"),
        ("truncated_body", canonical[:last_end - 1], ".batch 2 (.body (.malformed .truncated))", "{}"),
        ("truncated_metadata", canonical[:second_body - 1], ".batch 1 (.envelope (.malformed .truncated))", "{}"),
        ("corrupt_record", corrupt, ".batch 1 (.metadata (.malformed .flatbuffer))", "{}"),
        ("bad_bitmap", bad_bitmap, ".batch 0 (.values (.malformed .validityBitmap))", "{}"),
        ("wrong_kind", canonical[:second_start] + primitive[:-8] + canonical[second_start:],
         ".batch 1 .expectedRecordBatch", "{}"),
        ("batch_limit", canonical, ".batch 1 .batchLimit", "{ batches := 1 }"),
        ("wrong_field", primitive, ".schemaBinding (.malformed .batchLayout)", "{}"),
        ("missing_schema", canonical[-8:], ".expectedSchema", "{}"),
    ):
        yield label, wire, rejection(wire, reason, limits)


LEAN = """module

meta import Silmaril.Formats.Arrow.TimestampStream.Defs
meta import Silmaril.Formats.Arrow.DateStream.Defs
meta import Silmaril.Formats.Arrow.Stream.Defs
meta import Silmaril.Formats.ColumnarTimestamp.Defs
meta import Silmaril.Numeric.Timestamp.Defs

open Silmaril Silmaril.Formats.Arrow Silmaril.Numeric.Timestamp

private meta def observes (limits : Limits) (wire : KBytes) (unit : SchemaReader.TimestampUnit)
    (timezone : Option String) (utc nullable : Bool) (scale : Int)
    (expected : List (List (Option Int))) : Bool :=
  match TimestampStream.read limits wire, DateStream.read {} wire, readStream {} wire with
  | .ok stream, .error (.unsupportedFieldType actual), .error (.unsupported (.fieldType 10)) =>
    let metadata := stream.binding.metadata
    let instant := match metadata.kind with | .utcInstant => true | .localReading => false
    stream.binding.name == "time" && stream.binding.nullable == nullable &&
      actual == .timestamp unit timezone && metadata.timezone == timezone &&
      metadata.unit.nanosecondsPerTick == scale && instant == utc &&
      stream.batches.map (List.map (Option.map Ticks.ticks)) == expected
  | _, _, _ => false

private meta def rejects (limits : Limits) (wire : KBytes) (expected : TimestampStream.Error) : Bool :=
  match TimestampStream.read limits wire with
  | .error actual => actual == expected
  | .ok _ => false
"""


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1"
    digest = hashlib.sha256()
    lines = [LEAN]
    for label, data, check in fixtures():
        digest.update(len(data).to_bytes(8, "little"))
        digest.update(data)
        lines.extend([f"-- {label}", check])
    assert digest.hexdigest() == FIXTURE_SHA256, f"fixture SHA-256 {digest.hexdigest()}"
    with tempfile.TemporaryDirectory() as temporary:
        driver = Path(temporary) / "Fixtures.lean"
        driver.write_text("\n".join(lines) + "\n", encoding="utf-8")
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", str(driver)], cwd=ROOT, check=True)
    print("PyArrow 26.0.1: 6 accepted streams and 10 typed failures passed, with legacy and DATE refusal")
    print(f"Length-framed fixture SHA-256 {FIXTURE_SHA256}")


if __name__ == "__main__":
    main()
