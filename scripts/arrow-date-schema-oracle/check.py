"""Check the Arrow Schema reader against pinned PyArrow metadata and mutations."""

import argparse
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

meta import Silmaril.Formats.Arrow.Metadata.Defs

open Silmaril Silmaril.Formats.Arrow

private meta def agrees {α : Type} [DecidableEq α] (actual expected : Except Error α) : Bool :=
  match actual, expected with
  | .ok value, .ok wanted => decide (value = wanted)
  | .error error, .error wanted => error == wanted
  | _, _ => false
"""


def require(condition, message):
    if not condition:
        raise SystemExit(message)


def scalar(data, position, code):
    return struct.unpack_from("<" + code, data, position)[0]


def target(data, position):
    return position + scalar(data, position, "I")


def entry(data, table, index):
    # Inspect producer vtables only to identify the mutation positions.
    vtable = table - scalar(data, table, "i")
    displacement = 4 + 2 * index
    if displacement >= scalar(data, vtable, "H"):
        return None
    return vtable + displacement


def slot(data, table, index):
    position = entry(data, table, index)
    if position is None:
        return None
    displacement = scalar(data, position, "H")
    return table + displacement if displacement else None


def schema_table(data):
    return target(data, slot(data, target(data, 0), 2))


def date_payload(data, index):
    fields = target(data, slot(data, schema_table(data), 1))
    field = target(data, fields + 4 + 4 * index)
    require(scalar(data, slot(data, field, 2), "B") == 8, "expected Date union tag 8")
    return target(data, slot(data, field, 3))


def raw_unit(data, index):
    position = slot(data, date_payload(data, index), 0)
    return None if position is None else scalar(data, position, "H")


def set_unit(data, index, code):
    changed = bytearray(data)
    position = slot(changed, date_payload(changed, index), 0)
    require(position is not None, "test mutation requires a present unit slot")
    struct.pack_into("<H", changed, position, code)
    return bytes(changed)


def set_endian(data, code):
    # Reuse the producer Schema's custom-metadata reference slot as an inline
    # short, and clear the old vtable entry. The old vector becomes unreachable.
    changed = bytearray(data)
    schema = schema_table(changed)
    old_entry = entry(changed, schema, 2)
    new_entry = entry(changed, schema, 0)
    old_slot = slot(changed, schema, 2)
    require(old_slot is not None and slot(changed, schema, 0) is None, "expected spare metadata slot")
    struct.pack_into("<H", changed, new_entry, old_slot - schema)
    struct.pack_into("<H", changed, old_entry, 0)
    struct.pack_into("<H", changed, old_slot, code)
    return bytes(changed)


def messages(pa, schema, batch=None):
    sink = pa.BufferOutputStream()
    with pa.ipc.new_stream(sink, schema) as writer:
        if batch is not None:
            writer.write_batch(batch)
    return [message.metadata.to_pybytes()
            for message in pa.ipc.MessageReader.open_stream(sink.getvalue())]


def fixtures(pa):
    dates = pa.schema([pa.field("day", pa.date32(), False), pa.field("milliseconds", pa.date64())])
    mixed = pa.schema([pa.field("row", pa.int32(), False), pa.field("日", pa.date32()),
                       pa.field("étiquette", pa.string()), pa.field("fin", pa.date64(), False)])
    legacy = pa.schema([pa.field("row", pa.int32(), False), pa.field("text", pa.string())])
    date_bytes, = messages(pa, dates)
    mixed_bytes, = messages(pa, mixed)
    row = pa.record_batch([pa.array([1], pa.int32()), pa.array(["x"])], schema=legacy)
    legacy_bytes, record = messages(pa, legacy, row)
    spare, = messages(pa, dates.with_metadata({b"spare": b"endianness fixture slot"}))
    require(raw_unit(date_bytes, 0) == 0, "producer did not explicitly write DAY")
    require(raw_unit(date_bytes, 1) is None, "producer did not omit the MILLISECOND default")
    explicit = set_unit(date_bytes, 0, 1)
    require(raw_unit(explicit, 0) == 1, "explicit MILLISECOND mutation failed")
    return {
        "dates": date_bytes,
        "mixed": mixed_bytes,
        "legacy": legacy_bytes,
        "explicit_millisecond": explicit,
        "big_endian": set_endian(spare, 1),
        "invalid_unit": set_unit(date_bytes, 0, 2),
        "invalid_endian": set_endian(spare, 2),
        "schema_custom_metadata": spare,
        "record_message": record,
    }


def observe_schema(pa, data):
    framed = struct.pack("<II", 0xFFFFFFFF, len(data)) + data
    return pa.ipc.read_schema(pa.BufferReader(framed))


def fields_term(pa, schema, legacy):
    types = {
        pa.int32(): (".int32", ".primitive .int32"),
        pa.string(): (".utf8", ".primitive .utf8"),
        pa.date32(): (None, ".date .day"),
        pa.date64(): (None, ".date .millisecond"),
    }
    fields = []
    for field in schema:
        kind = types[field.type][0 if legacy else 1]
        label = json.dumps(field.name, ensure_ascii=False)
        nullable = str(field.nullable).lower()
        fields.append(f"⟨{label}, {nullable}, {kind}⟩")
    return "[" + ", ".join(fields) + "]"


def bytes_term(data):
    return f"(KBytes.leaf {len(data)} {int.from_bytes(data, 'little')})"


def lean_checks(pa, name, data):
    wire = bytes_term(data)
    negative = {
        "invalid_unit": "(.malformed .flatbuffer)",
        "invalid_endian": "(.unsupported (.endianness 2))",
        "schema_custom_metadata": "(.unsupported .customMetadata)",
        "record_message": "(.unsupported (.messageKind 3))",
    }
    if name in negative:
        yield f"#guard agrees (SchemaReader.readMessage {{}} {wire}) (.error {negative[name]})"
        return
    observed = observe_schema(pa, data)
    endian = ".big" if name == "big_endian" else ".little"
    fields = fields_term(pa, observed, legacy=False)
    yield f"#guard agrees (SchemaReader.readMessage {{}} {wire}) (.ok ⟨{endian}, {fields}⟩)"
    if name == "legacy":
        legacy_fields = fields_term(pa, observed, legacy=True)
        yield f"#guard agrees (readMessage {{}} {wire}) (.ok ⟨.schema {legacy_fields}, 0⟩)"
    else:
        reason = ".endianness 1" if name == "big_endian" else ".fieldType 8"
        yield f"#guard agrees (readMessage {{}} {wire}) (.error (.unsupported ({reason})))"
    if name == "mixed":
        yield f"#guard agrees (SchemaReader.readMessage {{ fields := 3 }} {wire}) (.error (.limit .fields))"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--pyarrow-path", type=Path, help="Directory containing the pinned PyArrow wheel contents")
    args = parser.parse_args()
    if args.pyarrow_path is not None:
        sys.path.insert(0, str(args.pyarrow_path.resolve()))

    import pyarrow as pa

    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    producer = manifest["producer"]
    require(platform.python_implementation() == "CPython" and platform.python_version() == producer["cpython"],
            "Use the pinned CPython version")
    require(pa.__version__ == producer["pyarrow"], "Use the pinned PyArrow version")

    commands = [LEAN_DRIVER]
    for name, data in fixtures(pa).items():
        digest = hashlib.sha256(data).hexdigest()
        require({"bytes": len(data), "sha256": digest} == manifest["metadata"][name],
                f"{name}: pinned metadata differs")
        commands.extend(lean_checks(pa, name, data))
        print(f"PASS {name} {digest}", flush=True)
    with tempfile.TemporaryDirectory(prefix="silmaril-arrow-date-schema-") as scratch:
        driver = Path(scratch) / "Fixtures.lean"
        driver.write_text("\n".join(commands) + "\n", encoding="utf-8")
        subprocess.run(
            [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", driver],
            cwd=ROOT,
            check=True,
        )
    print(f"PASS {len(commands) - 1} Lean Schema observations and compatibility checks")


if __name__ == "__main__":
    main()
