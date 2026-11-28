"""Emit native LIST streams with Lean and verify them with pinned PyArrow."""

from hashlib import sha256
import os
from pathlib import Path
import runpy
import struct
import subprocess
import sys

import pyarrow as pa

here = Path(__file__).resolve().parent
wire = runpy.run_path(str(here.parent / "arrow-list-int32-stream" / "Oracle.py"))
scalar, target, slot, vector = (wire[name] for name in ("scalar", "target", "slot", "vector"))
EOS = bytes.fromhex("ff ff ff ff 00 00 00 00")
FIELD = "résultats"
CHILD = "élément"
BATCHES = [
    [None, [], [None], [-7, None, 0]],
    [],
    [[-(1 << 31), (1 << 31) - 1], None, []],
    [None, None],
]


def bitmap(slots):
    return bytes(sum(1 << bit for bit, value in enumerate(slots[start:start + 8])
                     if value is not None)
                 for start in range(0, len(slots), 8))


def check(path, expected):
    data = path.read_bytes()
    with pa.ipc.open_stream(data) as reader:
        assert reader.schema == pa.schema([pa.field(
            FIELD, pa.list_(pa.field(CHILD, pa.int32(), nullable=True)), nullable=True,
        )])
        batches = list(reader)
    assert [batch.column(0).to_pylist() for batch in batches] == expected
    assert [batch.num_rows for batch in batches] == list(map(len, expected))
    for batch in batches:
        batch.validate(full=True)

    print(f"{path.name}, SHA-256 {sha256(data).hexdigest()}")
    messages = list(pa.ipc.MessageReader.open_stream(data))
    assert [message.type for message in messages] == ["schema"] + ["record batch"] * len(expected)
    assert all(message.metadata_version == pa.ipc.MetadataVersion.V5 for message in messages)
    size = messages[0].metadata.size
    assert struct.unpack_from("<II", data, 0) == (0xFFFFFFFF, size)
    assert not messages[0].body
    offset = 8 + size
    print(f"schema [0, {offset}), {FIELD}: nullable List<{CHILD}: nullable signed Int32>")
    for message, rows in zip(messages[1:], expected, strict=True):
        metadata = message.metadata.to_pybytes()
        root = target(metadata, 0)
        batch = target(metadata, slot(metadata, root, 2))
        _, nodes = vector(metadata, batch, 1, "<qq")
        _, descriptors = vector(metadata, batch, 2, "<qq")
        assert struct.unpack_from("<II", data, offset) == (0xFFFFFFFF, len(metadata))
        body_start = offset + 8 + len(metadata)
        body = message.body.to_pybytes()
        stop = body_start + len(body)
        assert body == data[body_start:stop]

        children, cuts = [], [0]
        for row in rows:
            children.extend(row or [])
            cuts.append(len(children))
        assert nodes == [(len(rows), rows.count(None)), (len(children), children.count(None))]
        parts = [
            bitmap(rows), struct.pack("<" + "i" * len(cuts), *cuts), bitmap(children),
            struct.pack("<" + "i" * len(children), *(value or 0 for value in children)),
        ]
        assert len(descriptors) == len(parts)
        cursor = 0
        for (start, count), part in zip(descriptors, parts, strict=True):
            end = start + count
            next_offset = (end + 7) // 8 * 8
            assert (start, count) == (cursor, len(part))
            assert body[start:end] == part and body[end:next_offset] == bytes(next_offset - end)
            cursor = next_offset
        assert cursor == len(body)
        print(f"record [{offset}, {stop}), metadata {len(metadata)}, body @{body_start}+{len(body)}")
        print(f"  nodes {nodes}, descriptors {descriptors}, offsets {cuts}")
        print(f"  parent bits {parts[0].hex()}, child bits {parts[2].hex()}, rows {rows}")
        offset = stop
    assert data[offset:] == EOS
    print(f"EOS [{offset}, {len(data)})")


def main(output):
    assert sys.byteorder == "little" and pa.__version__ == "26.0.1"
    output = output.resolve()
    output.mkdir(exist_ok=True, parents=True)
    stream = output / "nullable-list-int32.arrows"
    schema_only = output / "schema-only.arrows"
    subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                    "-DwarningAsError=true", "--run", str(here / "Emit.lean"), str(stream), str(schema_only)],
                   cwd=here.parents[1], check=True)
    print(f"PyArrow {pa.__version__}")
    check(stream, BATCHES)
    check(schema_only, [])


if __name__ == "__main__":
    main(Path(sys.argv[1]))
