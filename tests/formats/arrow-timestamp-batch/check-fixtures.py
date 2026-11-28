"""Check normalized Timestamp Schema metadata and IPC bodies against pinned PyArrow."""

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
FB = run_path(str(ROOT / "scripts/arrow-date-schema-oracle/check.py"))
FIXTURE_SHA256 = "593365e8721d15144c95a7d8226545a1a1f872d0ce21abec029a49d53c450cde"
UNITS = {"s": ("second", 1_000_000_000), "ms": ("millisecond", 1_000_000),
         "us": ("microsecond", 1000), "ns": ("nanosecond", 1)}
MIXED = [-(2**63), None, -2001, -1, 0, None, 2**63 - 1]


def lean_bytes(data):
    return FB["bytes_term"](data)


def lean_zone(timezone):
    return "none" if timezone is None else f"(some {json.dumps(timezone)})"


def lean_ticks(values):
    return "[" + ", ".join("none" if value is None else f"some ({value})" for value in values) + "]"


def write_stream(unit, timezone, nullable=True, ticks=MIXED, metadata=None):
    type_ = pa.timestamp(unit, timezone)
    schema = pa.schema([pa.field("time", type_, nullable=nullable)], metadata=metadata)
    array = pa.array(ticks, type=pa.int64()).cast(type_)
    batch = pa.RecordBatch.from_arrays([array], schema=schema)
    ipc = FB["ipc_stream"](pa, schema, batch)
    observed = pa.ipc.open_stream(ipc).read_next_batch()
    assert observed.schema == batch.schema
    assert observed.column(0).cast(pa.int64()).to_pylist() == ticks
    message, record = list(pa.ipc.MessageReader.open_stream(ipc))
    return ipc.to_pybytes(), message.metadata.to_pybytes(), record.metadata.to_pybytes(), record.body.to_pybytes()


def payload(data):
    field = FB["field_table"](data, 0)
    assert FB["scalar"](data, FB["slot"](data, field, 2), "B") == 10
    return FB["target"](data, FB["slot"](data, field, 3))


def unit_at(data):
    return FB["slot"](data, payload(data), 0)


def timezone_at(data):
    position = FB["slot"](data, payload(data), 1)
    return None if position is None else FB["target"](data, position)


def update_hash(digest, data):
    digest.update(len(data).to_bytes(8, "little"))
    digest.update(data)


def check_batch(lines, schema, record, body, unit, timezone, nullable, ticks, negatives=False, stream=None):
    name, scale = UNITS[unit]
    lines.append(f"  checkBatch {lean_bytes(schema)} {lean_bytes(record)} {lean_bytes(body)} "
                 f".{name} {lean_zone(timezone)} {str(nullable).lower()} {scale} "
                 f"{lean_ticks(ticks)} {str(negatives).lower()}")
    if stream is not None:
        lines.append(f"  checkDateStream {lean_bytes(stream)} .{name} {lean_zone(timezone)}")


def checks(lines, digest):
    lines.append("private def fixtures : IO Unit := do")
    for unit_index, unit in enumerate(UNITS):
        for timezone in (None, "Asia/Kathmandu"):
            file, schema, record, body = write_stream(unit, timezone)
            raw = unit_at(schema)
            assert (None if raw is None else FB["scalar"](schema, raw, "H")) == (
                None if unit_index == 0 else unit_index)
            zone = timezone_at(schema)
            if timezone is None:
                assert zone is None
            else:
                assert FB["scalar"](schema, zone, "I") == len(timezone)
                assert schema[zone + 4:zone + 4 + len(timezone)] == timezone.encode()
            update_hash(digest, file)
            check_batch(lines, schema, record, body, unit, timezone, True, MIXED,
                        negatives=(unit == "ns" and timezone is None), stream=file)
    required = [-2001, -1, 0, 2**63 - 1]
    file, schema, record, body = write_stream("us", "+05:45", nullable=False, ticks=required)
    update_hash(digest, file)
    check_batch(lines, schema, record, body, "us", "+05:45", False, required, stream=file)

    _, schema, record, body = write_stream("ms", "Asia/Kathmandu")
    explicit_second = bytearray(schema)
    struct.pack_into("<H", explicit_second, unit_at(schema), 0)
    assert FB["observe_schema"](pa, explicit_second).field(0).type.unit == "s"
    empty_timezone = bytearray(schema)
    string = timezone_at(schema)
    struct.pack_into("<I", empty_timezone, string, 0)
    empty_timezone[string + 4] = 0
    assert FB["observe_schema"](pa, empty_timezone).field(0).type.tz in (None, "")
    for mutated, unit, timezone in ((explicit_second, "s", "Asia/Kathmandu"),
                                    (empty_timezone, "ms", "")):
        update_hash(digest, mutated)
        check_batch(lines, mutated, record, body, unit, timezone, True, MIXED)

    invalid_unit = bytearray(schema)
    struct.pack_into("<H", invalid_unit, unit_at(schema), 65535)
    invalid_utf8 = bytearray(schema)
    invalid_utf8[string + 4] = 255
    no_terminator = bytearray(schema)
    no_terminator[string + 4 + len("Asia/Kathmandu")] = 1
    _, spare, _, _ = write_stream("ms", "Asia/Kathmandu", metadata={b"spare": b"endian slot"})
    big = FB["set_endian"](spare, 1)
    for data, error in ((invalid_unit, ".malformed .flatbuffer"),
                        (invalid_utf8, ".malformed .invalidUtf8"),
                        (no_terminator, ".malformed .flatbuffer")):
        update_hash(digest, data)
        lines.append(f"  expectError (SchemaReader.readMessage {{}} {lean_bytes(data)}) ({error})")
    update_hash(digest, big)
    lines.extend([
        f"  let big ← require (SchemaReader.readMessage {{}} {lean_bytes(big)})",
        '  check (big.endianness == .big) "normalized endian"',
        '  expectError (TimestampBatch.bindSchema big) (.unsupported (.endianness 1))',
    ])


HARNESS = '''module
import Silmaril.Formats.Arrow.TimestampBatch.Defs
import Silmaril.Formats.Arrow.DateStream.Defs
meta import Silmaril.Formats.Arrow.DateBatch.Defs
meta import Silmaril.Formats.Arrow.DateStream.Defs
meta import Silmaril.Formats.Arrow.TimestampBatch.Defs
meta import Silmaril.Formats.Arrow.Metadata.Defs
meta import Silmaril.Formats.Arrow.Layout.Defs
meta import Silmaril.Formats.ColumnarTimestamp.Defs
meta import Silmaril.Numeric.Timestamp.Defs
meta import Silmaril.Prelude.Bytes.Defs
open Silmaril Silmaril.Formats.Arrow Silmaril.Numeric.Timestamp
private def check (test : Bool) (label : String) : IO Unit :=
  unless test do throw (IO.userError label)
private def require {α : Type} (result : Except Error α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError s!"{repr cause}")
private def expectError {α : Type} (result : Except Error α) (expected : Error) : IO Unit :=
  match result with
  | .error actual => check (actual == expected) s!"expected {repr expected}, got {repr actual}"
  | .ok _ => throw (IO.userError s!"accepted invalid batch for {repr expected}")
private def checkDateStream (stream : KBytes) (unit : SchemaReader.TimestampUnit)
    (timezone : Option String) : IO Unit :=
  let expected := DateStream.Error.unsupportedFieldType (.timestamp unit timezone)
  match DateStream.read {} stream with
  | .error actual => check (actual == expected) s!"expected {repr expected}, got {repr actual}"
  | .ok _ => throw (IO.userError "DATE stream admitted Timestamp")
private def checkFailures (binding : TimestampBatch.Binding) (message : Message) (body : KBytes) : IO Unit := do
  let .recordBatch batch := message.header | throw (IO.userError "expected batch")
  let [node] := batch.nodes | throw (IO.userError "expected node")
  let [bitmap, data] := batch.buffers | throw (IO.userError "expected buffers")
  let decode := TimestampBatch.decodeBatch {} binding
  expectError (decode { message with bodyLength := message.bodyLength + 8 } body) (.malformed .bodyLength)
  expectError (decode { message with bodyLength := body.len - 1 } (body.slice 0 (body.len - 1)))
    (.malformed .bodyLength)
  expectError (decode { message with header := .recordBatch { batch with buffers := [] } } body)
    (.malformed .batchLayout)
  let misaligned := { batch with buffers := [bitmap, { data with offset := data.offset + 1 }] }
  expectError (decode { message with header := .recordBatch misaligned } body) (.malformed .batchLayout)
  let short := { batch with buffers := [bitmap, { data with length := 1 }] }
  expectError (decode { message with header := .recordBatch short } body) (.malformed .bodyValues)
  let noBitmap := { batch with buffers := [{ bitmap with length := 0 }, data] }
  expectError (decode { message with header := .recordBatch noBitmap } body) (.malformed .validityBitmap)
  let wrongRows := { batch with nodes := [{ node with length := node.length - 1 }] }
  expectError (decode { message with header := .recordBatch wrongRows } body) (.malformed .batchLayout)
  expectError (TimestampBatch.decodeBatch {} { binding with nullable := false } message body)
    (.malformed .validityBitmap)
  expectError (TimestampBatch.decodeBatch { rows := 0 } binding message body) (.limit .rows)
  expectError (TimestampBatch.decodeBatch { bodyBytes := 0 } binding message body) (.limit .bodyBytes)
private def checkBatch (schema record body : KBytes) (unit : SchemaReader.TimestampUnit)
    (timezone : Option String) (nullable : Bool) (scale : Int) (expected : List (Option Int))
    (negatives : Bool) : IO Unit := do
  let decoded ← require (SchemaReader.readMessage {} schema)
  check (decoded == ⟨.little, [⟨"time", nullable, .timestamp unit timezone⟩]⟩) "normalized schema"
  expectError (readMessage {} schema) (.unsupported (.fieldType 10))
  check (match DateBatch.decode {} schema record body with
    | .error (.unsupportedFieldType actual) => actual == .timestamp unit timezone
    | _ => false) "DATE batch admission rejects Timestamp"
  let observed ← require (TimestampBatch.readBatch {} schema record body)
  check (observed.binding.name == "time" && observed.binding.nullable == nullable) "bound field"
  let metadata := observed.binding.metadata
  check (metadata.timezone == timezone && metadata.unit.nanosecondsPerTick == scale) "bound metadata"
  let utc := match metadata.kind with | .utcInstant => true | .localReading => false
  check (utc == (timezone.filter (· != "")).isSome) "epoch interpretation"
  check (observed.slots.map (Option.map Ticks.ticks) == expected) "wire slot order and signed counts"
  if negatives then checkFailures observed.binding (← require (readMessage {} record)) body
'''


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1"
    digest = hashlib.sha256()
    lines = [HARNESS]
    checks(lines, digest)
    assert digest.hexdigest() == FIXTURE_SHA256, f"fixture SHA-256 {digest.hexdigest()}"
    with tempfile.TemporaryDirectory() as temporary:
        driver = Path(temporary) / "Fixtures.lean"
        driver.write_text("\n".join(lines + ["#eval fixtures"]) + "\n", encoding="utf-8")
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", str(driver)], cwd=ROOT, check=True)
    print("PyArrow 26.0.1: 9 producer batches, explicit SECOND and empty-zone variants, and 14 rejection cases passed")
    print("DATE batch and stream both rejected all 9 producer fixtures with the exact normalized field type")
    print(f"Length-framed fixture SHA-256 {FIXTURE_SHA256}")


if __name__ == "__main__":
    main()
