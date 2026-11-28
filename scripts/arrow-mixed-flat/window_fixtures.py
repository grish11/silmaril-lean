#!/usr/bin/env python3
"""Produce and reopen a mixed Arrow V5 file in a wider immutable carrier."""
import argparse
import hashlib
from pathlib import Path
import runpy
import struct
import sys

import pyarrow as pa


ROOT = Path(__file__).resolve().parents[2]
FIXTURE = ROOT / "Silmaril/Formats/Arrow/MixedFlat/File/Window/Fixture.lean"
DIGEST = "f1c55f598ee91bf522d50e582121f977ed4c62cda5be64026b95dcda0215e9ee"


def produce():
    schema = pa.schema([pa.field("signed", pa.int32()), pa.field("octets", pa.binary_view())])
    values = [
        [[-7, None, 42, -(1 << 31)], [b"", None, b"\xff" * 12, bytes(range(13))]],
        [[], []],
        [[0, (1 << 31) - 1], [b"tail", None]],
    ]
    batches = [
        pa.record_batch(
            [pa.array(slots, type=field.type) for slots, field in zip(columns, schema, strict=True)],
            schema=schema,
        )
        for columns in values
    ]
    sink = pa.BufferOutputStream()
    sink.write(b"test enclosing prefix".ljust(64, b"\x99"))
    start = sink.tell()
    options = pa.ipc.IpcWriteOptions(metadata_version=pa.ipc.MetadataVersion.V5,
                                     use_legacy_format=False, compression=None)
    with pa.ipc.new_file(sink, schema, options=options) as writer:
        for batch in batches:
            writer.write_batch(batch)
    stop = sink.tell()
    sink.write(b"enclosing suffix")
    data = sink.getvalue().to_pybytes()

    assert hashlib.sha256(data).hexdigest() == DIGEST
    assert data[start:start+8] == b"ARROW1\0\0" and data[stop-6:stop] == b"ARROW1"
    length, = struct.unpack_from("<i", data, stop - 10)
    footer = stop - 10 - length
    assert data[footer-8:footer] == b"\xff\xff\xff\xff\0\0\0\0"
    assert (start, stop, footer, length) == (64, 1354, 1080, 264)

    wire = runpy.run_path(str(ROOT / "scripts/arrow-binary-view/batch_fixtures.py"))
    slot_at, target, vector_at = (wire[name] for name in ("slot_at", "target", "vector_at"))
    root = target(data, footer)
    vector, blocks = vector_at(data, slot_at(data, root, 3)[1], "<qi4xq")
    assert blocks == [(256, 232, 112), (600, 192, 0), (792, 232, 48)]
    schema_table = target(data, slot_at(data, root, 1)[1])
    fields_vector = target(data, slot_at(data, schema_table, 1)[1])
    first_field = target(data, fields_vector + 4)
    field_name = target(data, slot_at(data, first_field, 0)[1]) + 4
    assert data[field_name:field_name+7] == b"signed\0"

    embedded = pa.ipc.read_schema(pa.ipc.read_message(data[start+8:footer]))
    with pa.ipc.open_file(data, footer_offset=stop) as reader:
        assert reader.schema.equals(embedded, check_metadata=True)
        assert reader.schema.equals(schema, check_metadata=True)
        assert reader.num_record_batches == len(batches)
        selected = {}
        for index in [2, 0, 1]:
            batch = reader.get_batch(index)
            batch.validate(full=True)
            selected[index] = batch
        assert all(selected[i].equals(batch) for i, batch in enumerate(batches))

    for index, neighbor, offset, replacement, expected in [
        (0, 2, 572, b"\xff", "inlined prefix"),
        (2, 0, 1040, struct.pack("<I", 2**31), "negative size"),
    ]:
        damaged = data[:offset] + replacement + data[offset+len(replacement):]
        with pa.ipc.open_file(damaged, footer_offset=stop) as reader:
            unaffected = reader.get_batch(neighbor)
            unaffected.validate(full=True)
            assert unaffected.equals(batches[neighbor])
            empty = reader.get_batch(1)
            empty.validate(full=True)
            assert empty.equals(batches[1])
            try:
                reader.get_batch(index).validate(full=True)
            except pa.ArrowInvalid as error:
                assert expected in str(error)
            else:
                raise AssertionError("expected a selected-record validation error")
        print(f"index {index} corruption rejected, index {neighbor} recovered")

    print(f"file [{start}, {stop}), footer ({footer}, {length}), absolute blocks {blocks}, "
          f"rows {[len(batch) for batch in batches]}, SHA-256 {DIGEST}")
    return data, start, stop, footer, vector + 4, field_name


def main():
    if sys.byteorder != "little" or pa.__version__ != pa.cpp_build_info.version or pa.__version__ != "26.0.1":
        raise SystemExit("fixture requires little-endian PyArrow 26.0.1")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, help="save the original carrier")
    parser.add_argument("--write", action="store_true", help="write the Lean fixture module")
    args = parser.parse_args()
    data, start, stop, footer, first_block, name = produce()
    lines = [
        "module", "", "public import Silmaril.Prelude.Bytes.Defs", "",
        "/-! Exact carrier produced by scripts/arrow-mixed-flat/window_fixtures.py. -/", "",
        "@[expose] public section", "",
        "namespace Silmaril.Formats.Arrow.MixedFlat.File.Window.Fixture", "",
        "def carrier : KBytes :=",
        f"  .leaf {len(data)} 0x{int.from_bytes(data, 'little'):x}", "",
    ]
    for label, value in [
        ("start", start), ("stop", stop), ("footerStart", footer),
        ("firstBlockSlot", first_block), ("footerFieldName", name),
    ]:
        lines += [f"def {label} : Nat := {value}", ""]
    lines += ["end Silmaril.Formats.Arrow.MixedFlat.File.Window.Fixture", ""]
    text = "\n".join(lines)
    if args.write:
        FIXTURE.write_text(text, encoding="utf-8")
    elif FIXTURE.read_text(encoding="utf-8") != text:
        raise SystemExit("pinned PyArrow carrier differs from the Lean fixture")
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_bytes(data)


if __name__ == "__main__":
    main()
