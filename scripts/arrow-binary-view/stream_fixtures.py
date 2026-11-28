#!/usr/bin/env python3
"""Reproduce pinned PyArrow BinaryView and Utf8View IPC streams."""

import argparse
import hashlib
from pathlib import Path
import runpy
import struct
import sys


SCRIPT = Path(__file__).resolve()
FIXTURE = SCRIPT.parents[2] / "Silmaril/Formats/Arrow/BinaryView/Stream/Fixture.lean"
EOS = b"\xff\xff\xff\xff\x00\x00\x00\x00"


def produce():
    import pyarrow as pa

    reference = runpy.run_path(str(SCRIPT.with_name("fixtures.py")))
    if sys.byteorder != "little" or pa.__version__ != reference["PYARROW_VERSION"]:
        raise SystemExit("fixture requires little-endian PyArrow 26.0.1")
    options = pa.ipc.IpcWriteOptions(metadata_version=pa.ipc.MetadataVersion.V5,
                                     use_legacy_format=False, compression=None)
    output = [
        "module\n\npublic import Silmaril.Prelude.Bytes.Defs\n\n",
        "/-! Reproduced by scripts/arrow-binary-view/stream_fixtures.py. -/\n\n",
        "@[expose] public section\n\n",
        "namespace Silmaril.Formats.Arrow.BinaryView.Stream.Fixture\n\n",
    ]

    def fixture(label, field_name, physical_type, rows):
        schema = pa.schema([pa.field(field_name, physical_type)])
        sink = pa.BufferOutputStream()
        with pa.ipc.new_stream(sink, schema, options=options) as writer:
            for batch in rows:
                writer.write_batch(pa.record_batch([pa.array(batch, type=physical_type)], schema=schema))
        value = sink.getvalue().to_pybytes()
        reader = pa.ipc.open_stream(value)
        assert reader.schema.equals(schema)
        assert [batch.column(0).to_pylist() for batch in reader] == rows

        offset = 0
        spans = []
        for message in pa.ipc.MessageReader.open_stream(value):
            meta_size = message.metadata.size
            marker, declared = struct.unpack_from("<II", value, offset)
            start = offset + 8 + meta_size
            assert marker == 0xFFFFFFFF and declared == meta_size and start % 8 == 0
            spans.append((offset, start))
            offset = start + (message.body.size if message.body is not None else 0)
        assert len(spans) == len(rows) + 1 and value[offset:] == EOS
        if rows:
            assert spans[1][0] == spans[0][1]
            assert spans[-1][1] < offset
        print(f"{label}: SHA-256 {hashlib.sha256(value).hexdigest()}, "
              f"(envelope, body) offsets {spans}, EOS {offset}")
        output.append(f"def {label} : KBytes :=\n  .leaf {len(value)} 0x{int.from_bytes(value, 'little'):x}\n\n")
        if label == "binary":
            output.extend([
                f"def binarySchemaEnd : Nat := {spans[0][1]}\n",
                f"def binarySecondRecord : Nat := {spans[2][0]}\n",
                f"def binaryLastRecord : Nat := {spans[3][0]}\n",
                f"def binaryLastBody : Nat := {spans[3][1]}\n",
                f"def binaryEos : Nat := {offset}\n\n",
            ])

    fixture("binary", "blob", pa.binary_view(), [[None, b"\xff", b"0123456789abcdef"], [], [b"", b"tail"]])
    fixture("utf8", "text", pa.string_view(), [["α", None, "雪" * 6], [], ["", "tail", "🧪" * 4]])
    fixture("schemaOnly", "text", pa.string_view(), [])
    output.append("end Silmaril.Formats.Arrow.BinaryView.Stream.Fixture\n")
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
