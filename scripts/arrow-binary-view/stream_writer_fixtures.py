#!/usr/bin/env python3
"""Read Lean-emitted Arrow V5 view streams with pinned PyArrow."""

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
    yield "nullable", pa.field("blob", pa.binary_view()), [
        [None, b"", b"\xff" + bytes(11), b"\x01" + bytes(12)], [], [b"\x02"],
    ], [1, 0, 0]
    yield "required", pa.field("bytes雪", pa.binary_view(), nullable=False), [
        [b"\x03" + bytes(12), b""],
    ], [1]
    field = pa.field("empty", pa.binary_view(), nullable=False)
    yield "one-empty", field, [[]], [0]
    yield "schema-only", field, [], []
    yield "utf8", pa.field("text", pa.string_view()), [["", "é" * 6, "é" * 6 + "x", None], []], [1, 0]


def check_framing(data, records):
    end = 0
    kinds = []
    for message in pa.ipc.MessageReader.open_stream(data):
        assert end % 8 == 0
        marker, size = struct.unpack_from("<II", data, end)
        assert marker == 0xFFFFFFFF and size == message.metadata.size and size % 8 == 0
        end += 8 + size + (message.body.size if message.body is not None else 0)
        kinds.append(message.type)
    assert kinds == ["schema", *(["record batch"] * records)]
    assert data[end:] == EOS


def main():
    if sys.byteorder != "little" or pa.__version__ != pa.cpp_build_info.version or pa.__version__ != "26.0.1":
        raise SystemExit("requires little-endian PyArrow 26.0.1")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True, help="directory for the emitted streams")
    output = parser.parse_args().out.resolve()
    subprocess.run([
        os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
        "-DwarningAsError=true", "--run", str(DRIVER), str(output),
    ], cwd=ROOT, check=True)

    for label, field, expected, data_counts in expected_cases():
        data = (output / f"{label}.arrow").read_bytes()
        check_framing(data, len(expected))
        with pa.ipc.open_stream(data) as reader:
            assert reader.schema.equals(pa.schema([field]), check_metadata=True)
            batches = list(reader)
        for batch in batches:
            batch.validate(full=True)
        assert [batch.column(0).to_pylist() for batch in batches] == expected
        assert [len(batch.column(0).buffers()) - 2 for batch in batches] == data_counts
        print(f"{label}: rows {[len(batch) for batch in batches]}, variadic counts {data_counts}, "
              f"SHA-256 {hashlib.sha256(data).hexdigest()}")


if __name__ == "__main__":
    main()
