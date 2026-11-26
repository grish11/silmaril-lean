#!/usr/bin/env python3
"""Reproduce pinned PyArrow mixed-flat IPC streams and a late truncation."""

import argparse
import hashlib
from pathlib import Path
import runpy
import struct
import sys


ROOT = Path(__file__).resolve().parents[2]
FIXTURE = ROOT / "Silmaril/Formats/Arrow/MixedFlat/Stream/Fixture.lean"
EOS = b"\xff\xff\xff\xff\x00\x00\x00\x00"


def produce():
    import pyarrow as pa

    if sys.byteorder != "little" or pa.__version__ != "26.0.1":
        raise SystemExit("fixture requires little-endian PyArrow 26.0.1")
    wire = runpy.run_path(str(ROOT / "scripts/arrow-binary-view/batch_fixtures.py"))
    slot_at, target, vector_at = (wire[name] for name in ("slot_at", "target", "vector_at"))
    types = [pa.int32(), pa.binary_view(), pa.string(), pa.string_view()]
    schema = pa.schema([pa.field(name, kind) for name, kind in zip(["i", "b", "u", "v"], types)])
    first = pa.record_batch([
        pa.array([1, None, -7, 0], type=types[0]),
        pa.concat_arrays([pa.array([b"x" * 13, None], type=types[1]),
                          pa.array([b"", b"y" * 17], type=types[1])]),
        pa.array(["α", "", None, "last"], type=types[2]),
        pa.array([None, "", "short", "雪" * 6], type=types[3]),
    ], schema=schema)
    empty = pa.record_batch([pa.array([], type=kind) for kind in types], schema=schema)
    last = pa.record_batch([
        pa.array([42, None], type=types[0]),
        pa.array([b"", b"\xff"], type=types[1]),
        pa.array(["end", None], type=types[2]),
        pa.array(["Ω" * 7, ""], type=types[3]),
    ], schema=schema)
    options = pa.ipc.IpcWriteOptions(metadata_version=pa.ipc.MetadataVersion.V5,
                                     use_legacy_format=False, compression=None)

    def stream(batches):
        sink = pa.BufferOutputStream()
        with pa.ipc.new_stream(sink, schema, options=options) as writer:
            for batch in batches:
                writer.write_batch(batch)
        value = sink.getvalue().to_pybytes()
        reader = pa.ipc.open_stream(value)
        assert reader.schema.equals(schema)
        assert [batch.to_pylist() for batch in reader] == [batch.to_pylist() for batch in batches]
        assert value.endswith(EOS)
        return value

    multi = stream([first, empty, last])
    schema_only = stream([])
    messages = list(pa.ipc.MessageReader.open_stream(multi))
    assert [message.type for message in messages] == ["schema", "record batch", "record batch", "record batch"]
    schema_size = messages[0].metadata.size
    assert schema_only == multi[:8 + schema_size] + EOS
    ranges = []
    offset = 8 + schema_size
    for record in messages[1:]:
        metadata_size = record.metadata.size
        assert struct.unpack_from("<II", multi, offset) == (0xFFFFFFFF, metadata_size)
        body_length = record.body.size if record.body is not None else 0
        ranges.append((offset, metadata_size, body_length))
        offset += 8 + metadata_size + body_length
    assert multi[offset:] == EOS
    late_truncated = multi[:offset - 1]
    reader = pa.ipc.open_stream(late_truncated)
    assert reader.read_next_batch().to_pylist() == first.to_pylist()
    assert reader.read_next_batch().num_rows == 0
    try:
        reader.read_next_batch()
    except (OSError, pa.ArrowInvalid):
        pass
    else:
        raise AssertionError("expected PyArrow to reject the truncated final body")

    last_metadata = messages[-1].metadata.to_pybytes()
    root = struct.unpack_from("<I", last_metadata)[0]
    payload = target(last_metadata, slot_at(last_metadata, root, 2)[1])
    _, counts = vector_at(last_metadata, slot_at(last_metadata, payload, 4)[1], "<q")
    _, descriptors = vector_at(last_metadata, slot_at(last_metadata, payload, 2)[1], "<qq")
    preceding_descriptors = 2 + (2 + counts[0][0]) + 3
    views_offset, _ = descriptors[preceding_descriptors + 1]
    start, metadata_size, _ = ranges[-1]
    last_prefix = start + 8 + metadata_size + views_offset + 4
    assert struct.unpack_from("<i", multi, last_prefix - 4)[0] == len(("Ω" * 7).encode())

    output = [
        "module\n\npublic import Silmaril.Prelude.Bytes.Defs\n\n",
        "/-! Reproduced by scripts/arrow-mixed-flat/stream_fixtures.py. -/\n\n",
        "@[expose] public section\n\n",
        "namespace Silmaril.Formats.Arrow.MixedFlat.Stream.Fixture\n\n",
    ]
    for label, value in (("multi", multi), ("schemaOnly", schema_only)):
        output.append(f"def {label} : KBytes :=\n  .leaf {len(value)} 0x{int.from_bytes(value, 'little'):x}\n\n")
    output.append(f"def lateTruncated : KBytes := multi.slice 0 {len(late_truncated)}\n\n")
    output.append("def multiRanges : List (Nat × Nat × Nat) :=\n  ["
                  + ", ".join(f"({start}, {size}, {length})" for start, size, length in ranges) + "]\n\n")
    output.extend([
        f"def multiSchemaSize : Nat := {schema_size}\n",
        f"def multiEos : Nat := {offset}\n",
        f"def lastRecordOffset : Nat := {start}\n",
        f"def lastViewPrefix : Nat := {last_prefix}\n\n",
        "end Silmaril.Formats.Arrow.MixedFlat.Stream.Fixture\n",
    ])
    print(f"record offsets, metadata sizes and body lengths: {ranges}")
    for name, value in (("multi", multi), ("schemaOnly", schema_only), ("lateTruncated", late_truncated)):
        print(f"{name}: SHA-256 {hashlib.sha256(value).hexdigest()}")
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
