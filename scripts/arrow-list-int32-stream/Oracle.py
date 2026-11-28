"""Reproduce and inspect a native PyArrow nullable List<Int32> IPC stream."""

from hashlib import sha256
from pathlib import Path
import runpy
import struct
import sys

import pyarrow as pa

wire = runpy.run_path(str(Path(__file__).resolve().parents[1] / "arrow-date-schema-oracle" / "check.py"))
scalar, target, slot, field_table = (wire[name] for name in ("scalar", "target", "slot", "field_table"))
EOS = bytes.fromhex("ff ff ff ff 00 00 00 00")
ROWS = [[None, [], [-7, None, 0], [None]], [], [[], [-(1 << 31), (1 << 31) - 1]]]


def vector(data, table, index, fmt):
    first = target(data, slot(data, table, index))
    count = scalar(data, first, "I")
    stride = struct.calcsize(fmt)
    return first + 4, [struct.unpack_from(fmt, data, first + 4 + i * stride) for i in range(count)]


def write():
    list_type = pa.list_(pa.field("element", pa.int32(), nullable=True))
    schema = pa.schema([pa.field("items", list_type, nullable=True)])
    # Null parent 0 covers physical child 99. Its neighboring valid slot is an empty list.
    first = pa.ListArray.from_arrays(
        pa.array([0, 1, 1, 4, 5], type=pa.int32()),
        pa.array([99, -7, None, 0, None], type=pa.int32()),
        type=list_type,
        mask=pa.array([True, False, False, False]),
    )
    arrays = [first, pa.array([], type=list_type), pa.array(ROWS[2], type=list_type)]
    options = pa.ipc.IpcWriteOptions(metadata_version=pa.ipc.MetadataVersion.V5,
                                     use_legacy_format=False, compression=None)
    sink = pa.BufferOutputStream()
    with pa.ipc.new_stream(sink, schema, options=options) as writer:
        for array in arrays:
            writer.write_batch(pa.record_batch([array], schema=schema))
    source = sink.getvalue().to_pybytes()
    reader = pa.ipc.open_stream(source)
    assert reader.schema.equals(schema)
    observed = [batch.column(0).to_pylist() for batch in reader]
    assert observed == ROWS
    return source


def valid(bitmap, index):
    return not bitmap or bool(bitmap[index // 8] & (1 << (index % 8)))


def inspect(source):
    messages = list(pa.ipc.MessageReader.open_stream(source))
    assert [m.type for m in messages] == ["schema", "record batch", "record batch", "record batch"]
    schema = messages[0].metadata.to_pybytes()
    assert struct.unpack_from("<II", source, 0) == (0xFFFFFFFF, len(schema))
    parent = field_table(schema, 0)
    assert scalar(schema, slot(schema, parent, 2), "B") == 12
    assert scalar(schema, slot(schema, parent, 1), "B") == 1
    assert slot(schema, parent, 4) is None
    children_at, children = vector(schema, parent, 5, "<I")
    assert len(children) == 1
    child = target(schema, children_at)
    assert scalar(schema, slot(schema, child, 1), "B") == 1
    assert scalar(schema, slot(schema, child, 2), "B") == 2
    int_payload = target(schema, slot(schema, child, 3))
    width = slot(schema, int_payload, 0)
    assert scalar(schema, width, "i") == 32
    assert scalar(schema, slot(schema, int_payload, 1), "B") == 1
    print(f"schema [0, {8 + len(schema)}), nullable List tag 12 with nullable signed Int32 child")
    print(f"child width word @{8 + width}")

    offset = 8 + len(schema)
    ranges = []
    for message, expected in zip(messages[1:], ROWS, strict=True):
        metadata = message.metadata.to_pybytes()
        root = target(metadata, 0)
        assert scalar(metadata, slot(metadata, root, 0), "H") == 4
        assert scalar(metadata, slot(metadata, root, 1), "B") == 3
        batch = target(metadata, slot(metadata, root, 2))
        _, nodes = vector(metadata, batch, 1, "<qq")
        descriptor_start, descriptors = vector(metadata, batch, 2, "<qq")
        assert len(nodes) == 2 and len(descriptors) == 4
        assert struct.unpack_from("<II", source, offset) == (0xFFFFFFFF, len(metadata))
        body = message.body.to_pybytes()
        body_start = offset + 8 + len(metadata)
        stop = body_start + len(body)
        assert body == source[body_start:stop]
        parent_valid, offsets, child_valid, values = [body[at:at + length] for at, length in descriptors]
        (parent_count, parent_nulls), (child_count, child_nulls) = nodes
        cuts = list(struct.unpack("<" + "i" * (parent_count + 1), offsets))
        assert cuts[0] == 0 and cuts[-1] == child_count and cuts == sorted(cuts)
        words = list(struct.unpack("<" + "i" * child_count, values))
        children = [word if valid(child_valid, i) else None for i, word in enumerate(words)]
        rows = [children[cuts[i]:cuts[i + 1]] if valid(parent_valid, i) else None
                for i in range(parent_count)]
        assert rows == expected and rows.count(None) == parent_nulls and children.count(None) == child_nulls
        print(f"record [{offset}, {stop}), metadata {len(metadata)}, body @{body_start}+{len(body)}")
        print(f"  nodes {nodes}, buffers {descriptors}, offsets {cuts}, children {children}")
        print(f"  parent bits 0x{parent_valid.hex()}, child bits 0x{child_valid.hex()}, rows {rows}")
        ranges.append((offset + 8 + descriptor_start, body_start, descriptors))
        offset = stop
    assert source[offset:] == EOS
    print(f"EOS [{offset}, {len(source)})")

    descriptors_start, body_start, descs = ranges[0]
    parent_bits = body_start + descs[0][0]
    cuts_start = body_start + descs[1][0]
    child_bits = body_start + descs[2][0]
    child_descriptor = descriptors_start + 3 * 16
    controls = [
        ("non-32-bit child", 8 + width, 64),
        ("parent validity mismatch", parent_bits, 15),
        ("child validity mismatch", child_bits, 27),
        ("descending offsets", cuts_start + 4, 2),
        ("negative offset", cuts_start + 7, 128),
        ("out-of-bounds offset", cuts_start + 8, 6),
        ("wrong terminal child count", cuts_start + 16, 4),
        ("child data descriptor out of body", child_descriptor, 56),
    ]
    for label, position, replacement in controls:
        changed = bytearray(source)
        assert changed[position] != replacement
        changed[position] = replacement
        print(f"{label} @{position} = {replacement}, SHA-256 {sha256(changed).hexdigest()}")


if __name__ == "__main__":
    assert pa.__version__ == "26.0.1" and sys.byteorder == "little"
    output = write()
    print(f"PyArrow {pa.__version__}, SHA-256 {sha256(output).hexdigest()}")
    inspect(output)
    Path(sys.argv[1]).write_bytes(output)
