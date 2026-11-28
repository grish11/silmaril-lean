#!/usr/bin/env python3
"""Reproduce the pinned PyArrow one-field view Schema fixtures."""

import argparse
import hashlib
from pathlib import Path
import runpy
import struct


SCRIPT = Path(__file__).resolve()
ROOT = SCRIPT.parents[2]
FIXTURE = ROOT / "Silmaril/Formats/Arrow/BinaryView/Schema/Fixture.lean"


def change(buf, offset, value):
    updated = bytearray(buf)
    updated[offset] = value
    return bytes(updated)


def produce():
    import pyarrow as pa

    wire = runpy.run_path(str(SCRIPT.with_name("batch_fixtures.py")))
    date_fixtures = runpy.run_path(str(ROOT / "scripts/arrow-date-schema-oracle/check.py"))
    slot_at, target = wire["slot_at"], wire["target"]
    batches = wire["producer_batches"](pa)
    required_schema = pa.schema([pa.field("vé", pa.string_view(), nullable=False)])
    required = pa.record_batch([pa.array(["", "雪" * 6], type=pa.string_view())], schema=required_schema)

    def message(schema):
        return next(pa.ipc.MessageReader.open_stream(wire["ipc_stream"](pa, schema))).metadata.to_pybytes()

    def field_table(buf):
        root = struct.unpack_from("<I", buf)[0]
        schema = target(buf, slot_at(buf, root, 2)[1])
        fields = target(buf, slot_at(buf, schema, 1)[1])
        return target(buf, fields + 4)

    output = [
        "module\n\npublic import Silmaril.Prelude.Bytes.Defs\n\n",
        "/-! Reproduced by scripts/arrow-binary-view/schema_fixtures.py. -/\n\n",
        "@[expose] public section\n\n",
        "namespace Silmaril.Formats.Arrow.BinaryView.Schema.Fixture\n\n",
    ]

    def fixture(name, value):
        output.append(f"def {name} : KBytes :=\n  .leaf {len(value)} 0x{int.from_bytes(value, 'little'):x}\n\n")
        print(f"{name}: SHA-256 {hashlib.sha256(value).hexdigest()}")

    for name, record, tag in (
        ("binary", batches["binary"], 23), ("mixed", batches["mixed"], 24),
        ("empty", batches["empty"], 23), ("required", required, 24),
    ):
        stream = wire["ipc_stream"](pa, record.schema, record)
        schema, batch = pa.ipc.MessageReader.open_stream(stream)
        readback = pa.ipc.open_stream(stream).read_next_batch()
        assert readback.schema.equals(record.schema) and readback.to_pylist() == record.to_pylist()
        value = schema.metadata.to_pybytes()
        field = field_table(value)
        type_slot = slot_at(value, field, 2)[1]
        type_table = target(value, slot_at(value, field, 3)[1])
        type_vtable = type_table - struct.unpack_from("<i", value, type_table)[0]
        assert value[type_slot] == tag and struct.unpack_from("<H", value, type_vtable)[0] == 4
        fixture(name + "Schema", value)
        if name == "required":
            fixture("requiredMetadata", batch.metadata.to_pybytes())
            fixture("requiredBody", batch.body.to_pybytes())
        if name == "binary":
            name_string = target(value, slot_at(value, field, 0)[1])
            fixture("badNameSchema", change(value, name_string + 4, 255))

    primitive = message(batches["primitive"].schema)
    fixture("primitiveSchema", primitive)
    type_slot = slot_at(primitive, field_table(primitive), 2)[1]
    fixture("wrongPayloadSchema", change(primitive, type_slot, 23))
    spare = message(batches["mixed"].schema.with_metadata({b"spare": b"endianness fixture slot"}))
    fixture("bigEndianSchema", date_fixtures["set_endian"](spare, 1))
    fixture("noFieldsSchema", message(pa.schema([])))
    fixture("twoFieldsSchema", message(pa.schema([pa.field("a", pa.binary_view()),
                                                   pa.field("b", pa.string_view())])))
    output.append("end Silmaril.Formats.Arrow.BinaryView.Schema.Fixture\n")
    return "".join(output)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", type=Path, help="write the reproduced Lean fixture to this path")
    args = parser.parse_args()
    reproduced = produce()
    if args.write:
        args.write.write_text(reproduced, encoding="utf-8")
    elif FIXTURE.read_text(encoding="utf-8") != reproduced:
        raise SystemExit("reproduced fixture differs from checked Lean bytes")


if __name__ == "__main__":
    main()
