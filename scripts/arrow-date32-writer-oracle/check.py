"""Independent PyArrow readback and physical-body checks for the Date32 emitter."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import struct
import subprocess
import sys
import tempfile


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
MIN = -(2**31)
MAX = 2**31 - 1
CASES = {
    "nullable": ("日付", True, [[MIN, -1, None, 0, 1, 11016, MAX, None, -719528, -25508],
                             [], [None, -2, 0]]),
    "required": ("époque", False, [[-719528, -1], [0, 11016]]),
    "schema_only": ("日付", False, []),
    "empty_batch": ("field", False, [[]]),
}


def hash_bytes(data):
    return {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}


def reference(pa, name, nullable, batches):
    schema = pa.schema([pa.field(name, pa.date32(), nullable=nullable)])
    sink = pa.BufferOutputStream()
    with pa.ipc.new_stream(sink, schema) as writer:
        for slots in batches:
            values = pa.array(slots, type=pa.int32()).view(pa.date32())
            writer.write_batch(pa.RecordBatch.from_arrays([values], schema=schema))
    return schema, sink.getvalue().to_pybytes()


def observe(pa, wire, schema, batches):
    with pa.ipc.open_stream(wire) as reader:
        assert reader.schema == schema
        read = [batch.column(0).view(pa.int32()).to_pylist() for batch in reader]
    assert read == batches


def uoffset(data, pos):
    return pos + struct.unpack_from("<I", data, pos)[0]


def slot(data, table, index):
    start = table - struct.unpack_from("<i", data, table)[0]
    vtable_size = struct.unpack_from("<H", data, start)[0]
    entry = 4 + index * 2
    if entry + 2 > vtable_size:
        return None
    offset = struct.unpack_from("<H", data, start + entry)[0]
    return table + offset if offset else None


def checked_day_schema(metadata):
    message = uoffset(metadata, 0)
    schema = uoffset(metadata, slot(metadata, message, 2))
    fields = uoffset(metadata, slot(metadata, schema, 1))
    assert struct.unpack_from("<I", metadata, fields)[0] == 1
    field = uoffset(metadata, fields + 4)
    assert metadata[slot(metadata, field, 2)] == 8
    date = uoffset(metadata, slot(metadata, field, 3))
    day = slot(metadata, date, 0)
    assert day is not None and struct.unpack_from("<h", metadata, day)[0] == 0


def pad(data):
    return data + bytes((-len(data)) % 8)


def physical(slots):
    bitmap = bytearray((len(slots) + 7) // 8)
    for index, cell in enumerate(slots):
        if cell is not None:
            bitmap[index // 8] |= 1 << (index % 8)
    words = b"".join(struct.pack("<i", 0 if cell is None else cell) for cell in slots)
    return bytes(bitmap), words


def check_record(message, slots):
    metadata = message.metadata.to_pybytes()
    table = uoffset(metadata, 0)
    batch = uoffset(metadata, slot(metadata, table, 2))
    nodes = uoffset(metadata, slot(metadata, batch, 1))
    buffers = uoffset(metadata, slot(metadata, batch, 2))
    assert struct.unpack_from("<Iqq", metadata, nodes) == (1, len(slots), slots.count(None))
    bitmap, words = physical(slots)
    descriptors = (2, 0, len(bitmap), len(pad(bitmap)), len(words))
    assert struct.unpack_from("<Iqqqq", metadata, buffers) == descriptors
    observed = message.body.to_pybytes() if message.body is not None else b""
    assert observed == pad(bitmap) + pad(words)


def lean_batches(batches):
    return "[" + ", ".join(
        "[" + ", ".join("none" if day is None else f"some (Int32.ofInt ({day}))"
                         for day in batch) + "]"
        for batch in batches
    ) + "]"


def emit(path, name, nullable, batches):
    lean_name = json.dumps(name, ensure_ascii=False)
    lean_path = json.dumps(str(path), ensure_ascii=False)
    source = f"""module

meta import Silmaril.Formats.Arrow.DateStream.Writer.Defs

open Silmaril.Formats.Arrow.DateStream.Writer

#eval do
  let .ok wire := emit {{}} {lean_name} {str(nullable).lower()} {lean_batches(batches)}
    | throw (IO.userError "Date32 emission failed")
  IO.FS.writeBinFile {lean_path} wire.toByteArray
"""
    driver = path.with_suffix(".lean")
    driver.write_text(source, encoding="utf-8")
    subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                    "-DwarningAsError=true", str(driver)], cwd=ROOT, check=True)
    return path.read_bytes()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pyarrow-path", type=Path, help="Directory containing unpacked PyArrow")
    parser.add_argument("--regenerate", action="store_true", help="Write pinned reference observations")
    args = parser.parse_args()
    if args.pyarrow_path is not None:
        sys.path.insert(0, str(args.pyarrow_path.resolve()))
    import pyarrow as pa

    assert sys.implementation.name == "cpython" and sys.version_info[:3] == (3, 13, 5)
    assert pa.__version__ == "26.0.1"
    manifest = {
        "cpython": "3.13.5", "pyarrow": pa.__version__,
        "pyarrow_wheel_sha256": "f71221bbc7707e3fad920d0478db9350791d4714ec445299ee0d56559fbc156c",
        "cases": {},
    }
    with tempfile.TemporaryDirectory(prefix="arrow-date32-writer-") as directory:
        for label, (name, nullable, batches) in CASES.items():
            schema, upstream = reference(pa, name, nullable, batches)
            observe(pa, upstream, schema, batches)
            manifest["cases"][label] = {
                "field": name, "nullable": nullable, "signed_slots": batches,
                "pyarrow_reference": hash_bytes(upstream),
                "expected_bodies": [hash_bytes(b"".join(map(pad, physical(batch)))) for batch in batches],
            }
            if not args.regenerate:
                wire = emit(Path(directory) / f"{label}.arrow", name, nullable, batches)
                observe(pa, wire, schema, batches)
                assert wire[-8:] == b"\xff\xff\xff\xff\0\0\0\0"
                messages = list(pa.ipc.MessageReader.open_stream(wire))
                assert len(messages) == 1 + len(batches)
                assert messages[0].type == "schema"
                checked_day_schema(messages[0].metadata.to_pybytes())
                for message, batch in zip(messages[1:], batches, strict=True):
                    assert message.type == "record batch"
                    check_record(message, batch)

    path = HERE / "fixtures.json"
    if args.regenerate:
        path.write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    else:
        assert manifest == json.loads(path.read_text(encoding="utf-8"))
        body_count = sum(len(batches) for _, _, batches in CASES.values())
        print(f"PASS {len(CASES)} emitted Date32 streams and {body_count} exact physical bodies")


if __name__ == "__main__":
    main()
