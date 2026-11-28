"""Exercise the checked DATE value boundary with pinned PyArrow arrays and IPC batches."""

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
LEAN_DRIVER = """\
module

meta import Silmaril.Formats.Arrow.DateValues.Defs

open Silmaril Silmaril.Formats.Arrow
open Silmaril.Formats.Arrow.DateValues (Descriptor View)

private meta def checkBatch (unit : DateValues.Unit) (descriptor : Descriptor)
    (metadata body : KBytes) (dates : DateValues.Column) : IO Unit := do
  let .ok message := readMessage {} metadata
    | throw (IO.userError "PyArrow record metadata was rejected")
  let .recordBatch batch := message.header
    | throw (IO.userError "expected record batch metadata")
  unless message.bodyLength == body.len do
    throw (IO.userError "body length differs from record metadata")
  unless DateValues.decodeBatch {} unit descriptor batch body == .ok dates do
    throw (IO.userError "DATE body observation differs from PyArrow")
  let [bitmap, values] := batch.buffers
    | throw (IO.userError "expected two buffers")
  let outside := { batch with buffers := [bitmap, { values with length := body.len + 1 }] }
  unless DateValues.decodeBatch {} unit descriptor outside body == .error (.ipc (.malformed .batchLayout)) do
    throw (IO.userError "out-of-body descriptor was accepted")
  let unsupportedEndian := { descriptor with endianness := 1 }
  unless DateValues.decodeBatch {} unit unsupportedEndian batch body ==
      .error (.ipc (.unsupported (.endianness 1))) do
    throw (IO.userError "wrong endianness was accepted")
  if unit == .millisecond then
    unless DateValues.decodeBatch {} .day descriptor batch body == .error (.wrongUnit .day 1) do
      throw (IO.userError "Date64 metadata was accepted by Date32")

"""


def require(condition, message):
    if not condition:
        raise SystemExit(message)


def make_fixture(pa, day_counts, case):
    date_type = pa.date32() if case["unit"] == "day" else pa.date64()
    values = [None if day is None else EPOCH + timedelta(days=day) for day in day_counts]
    array = pa.array(values, type=date_type).slice(case["start"], case["length"])
    array.validate(full=True)
    observed = array.to_pylist()
    require(observed == values[case["start"]:case["start"] + case["length"]],
            "PyArrow in-memory slice does not match the requested window")
    bitmap, payload = [buffer.to_pybytes() for buffer in array.buffers()]
    batch = pa.record_batch([array], names=["date"])
    sink = pa.BufferOutputStream()
    with pa.ipc.new_stream(sink, batch.schema) as writer:
        writer.write_batch(batch)
    wire = sink.getvalue()
    read = pa.ipc.open_stream(wire).read_next_batch().column(0)
    require(read.type == date_type and read.to_pylist() == observed, "PyArrow IPC changed the sliced dates")
    _, message = list(pa.ipc.MessageReader.open_stream(wire))
    require(message.type == "record batch", "expected a PyArrow record batch")
    return observed, {
        "ipc": wire.to_pybytes(),
        "bitmap": bitmap,
        "values": payload,
        "metadata": message.metadata.to_pybytes(),
        "body": message.body.to_pybytes(),
    }


def byte_term(wire):
    return f"(KBytes.leaf {len(wire)} {int.from_bytes(wire, 'little')})"


def dates_term(observed):
    return "[" + ", ".join(
        "none" if value is None else f"some ⟨{value.year}, {value.month}, {value.day}⟩"
        for value in observed
    ) + "]"


def view_term(case, observed, bitmap, values):
    null_count = observed.count(None)
    return f"(⟨{case['start']}, ⟨{len(observed)}, {null_count}⟩, {byte_term(bitmap)}, {byte_term(values)}⟩ : View)"


def fractional_payload(pa, case, observed, bitmap, values, slot, valid):
    patched = bytearray(values)
    struct.pack_into("<q", patched, 8 * (case["start"] + slot), 1)
    array = pa.Array.from_buffers(pa.date64(), len(observed),
                                  [pa.py_buffer(bitmap), pa.py_buffer(patched)], offset=case["start"])
    try:
        array.validate(full=True)
    except pa.ArrowInvalid as error:
        require(valid and "whole number of days" in str(error), "unexpected PyArrow validation error")
    else:
        require(not valid and array.to_pylist() == observed, "PyArrow did not mask the fractional word")
    return patched


def lean_checks(pa, case, observed, parts):
    unit = "." + case["unit"]
    unit_code = int(case["unit"] == "millisecond")
    descriptor = f"(⟨8, {unit_code}, 0, true⟩ : Descriptor)"
    bitmap, values = parts["bitmap"], parts["values"]
    view = view_term(case, observed, bitmap, values)
    dates = dates_term(observed)
    decoder = f"DateValues.decode {{}} {unit} {descriptor}"
    yield f"#guard {decoder} {view} = .ok {dates}"
    yield f"#eval checkBatch {unit} {descriptor} {byte_term(parts['metadata'])} {byte_term(parts['body'])} {dates}"
    require(case["start"] + len(observed) > 8, "bitmap control must cross a byte boundary")
    short_bitmap = view_term(case, observed, bitmap[:1], values)
    yield f"#guard {decoder} {short_bitmap} = .error (.ipc (.malformed .validityBitmap))"
    width = 8 if unit_code else 4
    last_byte = width * (case["start"] + len(observed))
    short_values = view_term(case, observed, bitmap, values[:last_byte - 1])
    yield f"#guard {decoder} {short_values} = .error (.ipc (.malformed .bodyValues))"
    if unit_code:
        valid_slot = next(index for index, value in enumerate(observed) if value is not None)
        patched = fractional_payload(pa, case, observed, bitmap, values, valid_slot, True)
        bad_view = view_term(case, observed, bitmap, patched)
        yield f"#guard {decoder} {bad_view} = .error (.nonWholeDay {valid_slot})"
        null_slot = observed.index(None)
        patched = fractional_payload(pa, case, observed, bitmap, values, null_slot, False)
        masked = view_term(case, observed, bitmap, patched)
        yield f"#guard {decoder} {masked} = .ok {dates}"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--pyarrow-path", type=Path, help="Directory containing the pinned PyArrow wheel contents")
    args = parser.parse_args()
    if args.pyarrow_path is not None:
        sys.path.insert(0, str(args.pyarrow_path.resolve()))

    import pyarrow as pa

    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    oracle = manifest["oracle"]
    require(platform.python_implementation() == "CPython" and platform.python_version() == oracle["cpython"],
            "Use the pinned CPython version")
    require(pa.__version__ == oracle["pyarrow"], "Use the pinned PyArrow version")

    commands = [LEAN_DRIVER]
    for case in manifest["cases"]:
        observed, parts = make_fixture(pa, manifest["source_epoch_days"], case)
        expected = case["artifacts"]
        for name, payload in parts.items():
            digest = hashlib.sha256(payload).hexdigest()
            require({"bytes": len(payload), "sha256": digest} == expected[name],
                    f"{case['unit']}: pinned {name} differs")
        commands.extend(lean_checks(pa, case, observed, parts))
        print(f"PASS {case['unit']} {len(observed)} slots {expected['ipc']['sha256']}", flush=True)

    with tempfile.TemporaryDirectory(prefix="silmaril-arrow-date-values-") as scratch:
        driver = Path(scratch) / "Fixtures.lean"
        driver.write_text("\n".join(commands) + "\n", encoding="utf-8")
        subprocess.run(
            [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", driver],
            cwd=ROOT,
            check=True,
        )
    print(f"PASS {len(commands) - 1} Lean fixture checks, including checked record bodies and negative controls")


if __name__ == "__main__":
    main()
