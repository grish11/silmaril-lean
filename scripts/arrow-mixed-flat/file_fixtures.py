#!/usr/bin/env python3
"""Reproduce the mixed-flat V5 file fixtures with pinned PyArrow."""

import argparse
import hashlib
from pathlib import Path
import runpy
import struct
import sys


ROOT = Path(__file__).resolve().parents[2]
FIXTURE = ROOT / "Silmaril/Formats/Arrow/MixedFlat/File/Fixture.lean"
MAGIC = b"ARROW1"
EOS = b"\xff\xff\xff\xff\x00\x00\x00\x00"


def produce():
    import pyarrow as pa

    if sys.byteorder != "little" or pa.__version__ != pa.cpp_build_info.version or pa.__version__ != "26.0.1":
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

    def emit(batches):
        sink = pa.BufferOutputStream()
        with pa.ipc.new_file(sink, schema, options=options) as writer:
            for batch in batches:
                writer.write_batch(batch)
        data = sink.getvalue().to_pybytes()
        with pa.ipc.open_file(data) as reader:
            assert reader.schema.equals(schema)
            assert reader.num_record_batches == len(batches)
            observed = [reader.get_batch(index) for index in range(reader.num_record_batches)]
            assert [batch.num_rows for batch in observed] == [batch.num_rows for batch in batches]
            assert [batch.to_pylist() for batch in observed] == [batch.to_pylist() for batch in batches]
        assert data.startswith(MAGIC + b"\0\0") and data.endswith(MAGIC)
        footer_size, = struct.unpack_from("<i", data, len(data) - 10)
        footer_start = len(data) - 10 - footer_size
        assert 0 < footer_size and footer_start % 8 == 0
        footer = data[footer_start:-10]
        root, = struct.unpack_from("<I", footer)
        assert struct.unpack_from("<h", footer, slot_at(footer, root, 0)[1])[0] == 4
        dictionary_slot = slot_at(footer, root, 2)
        if dictionary_slot is not None:
            assert vector_at(footer, dictionary_slot[1], "<qi4xq")[1] == []
        block_slot = slot_at(footer, root, 3)
        vector, blocks = vector_at(footer, block_slot[1], "<qi4xq") if block_slot else (0, [])
        stream = data[8:footer_start]
        with pa.ipc.open_stream(stream) as reader:
            assert reader.schema.equals(schema, check_metadata=True)
            streamed = list(reader)
        row_counts = [batch.num_rows for batch in batches]
        assert [batch.num_rows for batch in streamed] == row_counts
        for indexed, sequential in zip(observed, streamed, strict=True):
            indexed.validate(full=True)
            sequential.validate(full=True)
            for positions in ([3, 0, 3, 1], []):
                projected = indexed.select(positions)
                stream_projected = sequential.select(positions)
                assert projected.num_rows == stream_projected.num_rows == indexed.num_rows
                assert projected.equals(stream_projected, check_metadata=True)
        print(f"indexed and embedded stream projections [3, 0, 3, 1] and [] preserve batch rows {row_counts}")

        messages = list(pa.ipc.MessageReader.open_stream(stream))
        assert [msg.type for msg in messages] == ["schema"] + ["record batch"] * len(batches)
        assert len(blocks) == len(batches)
        cursor = 16 + messages[0].metadata.size
        counts = []
        for (offset, metadata_length, body_length), message in zip(blocks, messages[1:]):
            assert offset == cursor and offset % 8 == 0
            assert (metadata_length, body_length) == (8 + message.metadata.size, message.body.size)
            assert struct.unpack_from("<II", data, offset) == (0xFFFFFFFF, metadata_length - 8)
            metadata = message.metadata.to_pybytes()
            table, = struct.unpack_from("<I", metadata)
            payload = target(metadata, slot_at(metadata, table, 2)[1])
            _, entries = vector_at(metadata, slot_at(metadata, payload, 4)[1], "<q")
            counts.append([value for (value,) in entries])
            cursor += metadata_length + body_length
        assert data[cursor:footer_start] == EOS
        return data, footer_start, root, vector, blocks, counts

    multi, footer_start, root, vector, blocks, counts = emit([first, empty, last])
    schema_only, _, _, _, no_blocks, _ = emit([])
    assert counts == [[2, 1], [0, 0], [1, 1]] and no_blocks == []
    assert [len(first), len(empty), len(last)] == [4, 0, 2]
    third_block = footer_start + vector + 4 + 2 * 24
    third_offset, third_metadata, _ = blocks[2]
    record = multi[third_offset + 8:third_offset + third_metadata]
    message_table, = struct.unpack_from("<I", record)
    body_word = third_offset + 8 + slot_at(record, message_table, 3)[1]
    footer = multi[footer_start:-10]
    footer_schema = target(footer, slot_at(footer, root, 1)[1])
    field_vector = target(footer, slot_at(footer, footer_schema, 1)[1])
    field_table = target(footer, field_vector + 4)
    field_name = target(footer, slot_at(footer, field_table, 0)[1]) + 4
    assert footer[field_name:field_name + 2] == b"i\0"

    output = [
        "module\n\npublic import Silmaril.Formats.Arrow.Metadata.Defs\n\n",
        "/-! Reproduced by scripts/arrow-mixed-flat/file_fixtures.py. -/\n\n",
        "@[expose] public section\n\n",
        "namespace Silmaril.Formats.Arrow.MixedFlat.File.Fixture\n\n",
    ]
    for name, data in (("multi", multi), ("schemaOnly", schema_only)):
        print(f"{name}: SHA-256 {hashlib.sha256(data).hexdigest()}")
        output.append(f"def {name} : KBytes :=\n  .leaf {len(data)} 0x{int.from_bytes(data, 'little'):x}\n\n")
    output.append("def indexBlocks : List FileBlock :=\n  ["
                  + ", ".join(f"⟨{start}, {metadata}, {body}⟩" for start, metadata, body in blocks)
                  + "]\n\n")
    output.extend(f"def {name} : Nat := {value}\n" for name, value in (
        ("footerStart", footer_start), ("lastBlockSlot", third_block), ("lastBodyWord", body_word),
        ("footerFieldName", footer_start + field_name),
    ))
    output.append("\nend Silmaril.Formats.Arrow.MixedFlat.File.Fixture\n")
    print(f"footer start {footer_start}, blocks {blocks}, view counts {counts}")
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
