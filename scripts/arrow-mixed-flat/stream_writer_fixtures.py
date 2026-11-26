#!/usr/bin/env python3
"""Validate complete Lean-emitted mixed V5 streams with pinned PyArrow."""

import argparse
import hashlib
import os
from pathlib import Path
import struct
import subprocess
import sys

import pyarrow as pa


ROOT = Path(__file__).resolve().parents[2]
DRIVER = Path(__file__).with_name("StreamWriter.lean")
EOS = b"\xff\xff\xff\xff\x00\x00\x00\x00"


def expected_cases():
    integer = pa.field("signed雪", pa.int32())
    view = pa.field("blob", pa.binary_view())
    first_int = [1, None, -7, -(2**31)]
    first_view = [None, b"", b"\xff" + bytes(11), b"\x01\x02\x03\x04" + bytes(9)]
    last_int = [2**31 - 1, 0]
    last_view = [b"\xff" + bytes(11), b"\x02"]
    yield "int-first", [integer, view], [[first_int, first_view], [[], []], [last_int, last_view]]
    yield "view-first", [view, integer], [[first_view, first_int], [[], []], [last_view, last_int]]
    required = [view.with_nullable(False), integer.with_nullable(False)]
    yield "required", required, [[last_view, last_int]]
    mixed_nullability = [view, integer.with_nullable(False)]
    yield "schema-only", mixed_nullability, []
    yield "one-empty", mixed_nullability, [[[], []]]


def check_framing(data, records):
    offset = 0
    offsets = []
    kinds = []
    for message in pa.ipc.MessageReader.open_stream(data):
        marker, size = struct.unpack_from("<II", data, offset)
        assert offset % 8 == 0 and marker == 0xFFFFFFFF
        assert size == message.metadata.size and size % 8 == 0
        body = message.body.size if message.body is not None else 0
        assert body % 8 == 0
        offsets.append((offset, size, body))
        offset += 8 + size + body
        kinds.append(message.type)
    assert kinds == ["schema", *(["record batch"] * records)]
    assert data[offset:] == EOS
    return offsets


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

    for label, fields, expected in expected_cases():
        data = (output / f"{label}.arrow").read_bytes()
        offsets = check_framing(data, len(expected))
        schema = pa.schema(fields)
        with pa.ipc.open_stream(data) as reader:
            assert reader.schema.equals(schema, check_metadata=True)
            batches = list(reader)
        for batch in batches:
            batch.validate(full=True)
        assert [[column.to_pylist() for column in batch.columns] for batch in batches] == expected
        print(f"{label}: rows {[len(batch) for batch in batches]}, "
              f"(offset, metadata, body) {offsets}, SHA-256 {hashlib.sha256(data).hexdigest()}")


if __name__ == "__main__":
    main()
