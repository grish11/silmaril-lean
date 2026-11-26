#!/usr/bin/env python3
"""Read standalone Lean-emitted Arrow IPC V5 RecordBatches with pinned PyArrow."""

import argparse
import hashlib
import os
from pathlib import Path
import struct
import subprocess
import sys

import pyarrow as pa


ROOT = Path(__file__).resolve().parents[2]
DRIVER = Path(__file__).with_name("RecordWriter.lean")


def cases():
    int_field = pa.field("signed", pa.int32())
    view_field = pa.field("octets", pa.binary_view())
    integers = [1, None, -7, -(2**31)]
    octets = [None, b"", b"\xff" + bytes(11), b"\x01\x02\x03\x04" + bytes(9)]
    yield "int-first", [int_field, view_field], [integers, octets], 1
    yield "view-first", [view_field, int_field], [octets, integers], 1
    yield "inline", [view_field.with_nullable(False), int_field.with_nullable(False)], [
        [b"\xff" + bytes(11), b""], [2**31 - 1, 0],
    ], 0
    yield "empty", [int_field.with_nullable(False), view_field], [[], []], 0


def slot(metadata, table, index):
    vtable = table - struct.unpack_from("<i", metadata, table)[0]
    entry = 4 + 2 * index
    assert entry + 2 <= struct.unpack_from("<H", metadata, vtable)[0]
    offset = struct.unpack_from("<H", metadata, vtable + entry)[0]
    assert offset != 0
    return table + offset


def target(metadata, offset):
    return offset + struct.unpack_from("<I", metadata, offset)[0]


def vector(metadata, table, index, fmt):
    start = target(metadata, slot(metadata, table, index))
    count = struct.unpack_from("<I", metadata, start)[0]
    step = struct.calcsize(fmt)
    assert (start + 4) % 8 == 0
    return [struct.unpack_from(fmt, metadata, start + 4 + step * i) for i in range(count)]


def physical_sizes(fields, columns, count):
    sizes = []
    for field, column in zip(fields, columns, strict=True):
        rows = len(column)
        sizes.append((rows + 7) // 8)
        if field.type == pa.int32():
            sizes.append(4 * rows)
        else:
            sizes.append(16 * rows)
            if count:
                sizes.append(sum(len(value) for value in column if value is not None and len(value) > 12))
    return sizes


def check_record(data, fields, columns, count):
    source = pa.BufferReader(data)
    message = pa.ipc.read_message(source)
    assert message.type == "record batch" and source.tell() == len(data)
    marker, size = struct.unpack_from("<II", data)
    assert marker == 0xFFFFFFFF and size == message.metadata.size and size % 8 == 0

    metadata = message.metadata
    root = target(metadata, 0)
    assert struct.unpack_from("<h", metadata, slot(metadata, root, 0)) == (4,)  # V5
    record = target(metadata, slot(metadata, root, 2))
    assert struct.unpack_from("<q", metadata, slot(metadata, record, 0)) == (len(columns[0]),)
    assert vector(metadata, record, 1, "<qq") == [(len(c), c.count(None)) for c in columns]
    assert vector(metadata, record, 4, "<q") == [(count,)]
    descriptors = []
    offset = 0
    for length in physical_sizes(fields, columns, count):
        descriptors.append((offset, length))
        offset += (length + 7) // 8 * 8
    assert vector(metadata, record, 2, "<qq") == descriptors
    assert message.body.size == offset

    schema = pa.schema(fields)
    batch = pa.ipc.read_record_batch(message, schema)
    batch.validate(full=True)
    assert batch.schema.equals(schema, check_metadata=True)
    assert [column.to_pylist() for column in batch.columns] == columns
    assert [len(column.buffers()) - 2 for field, column in zip(fields, batch.columns, strict=True)
            if field.type == pa.binary_view()] == [count]
    return descriptors


def main():
    if sys.byteorder != "little" or pa.__version__ != pa.cpp_build_info.version or pa.__version__ != "26.0.1":
        raise SystemExit("requires little-endian PyArrow 26.0.1")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", required=True, type=Path)
    output = parser.parse_args().out.resolve()
    subprocess.run([
        os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
        "-DwarningAsError=true", "--run", str(DRIVER), str(output),
    ], cwd=ROOT, check=True)
    for label, fields, columns, count in cases():
        data = (output / f"{label}.arrow").read_bytes()
        descriptors = check_record(data, fields, columns, count)
        print(f"{label}: rows {len(columns[0])}, counts [{count}], descriptors {descriptors}, "
              f"SHA-256 {hashlib.sha256(data).hexdigest()}")


if __name__ == "__main__":
    main()
