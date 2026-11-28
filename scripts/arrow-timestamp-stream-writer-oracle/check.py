"""Read native Lean TIMESTAMP Schema frames and streams with pinned PyArrow."""

import hashlib
import os
from pathlib import Path
import platform
import struct
import subprocess
import tempfile

import pyarrow as pa

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "scripts/arrow-timestamp-stream-writer-oracle/Emit.lean"
EOS = struct.pack("<II", 0xFFFFFFFF, 0)
MIN, MAX = -(2**63), 2**63 - 1


def check_case(directory, name, unit, timezone, nullable, empty):
    schema_path = directory / "schema"
    stream_path = directory / "stream"
    subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DwarningAsError=true", "--run",
                    str(SOURCE), name, unit, timezone or "local", "optional" if nullable else "required",
                    "empty" if empty else "records", str(schema_path), str(stream_path)],
                   check=True, cwd=ROOT)
    expected_schema = pa.schema([pa.field(name, pa.timestamp(unit, timezone), nullable=nullable)])
    slot = None if nullable else -7
    expected_batches = [] if empty else [[MIN, slot, -1, 0, MAX], [], [slot, 87654321]]

    schema_wire = schema_path.read_bytes()
    marker, extent = struct.unpack_from("<II", schema_wire)
    assert marker == 0xFFFFFFFF and extent == len(schema_wire) - 8 and extent % 8 == 0
    schema_source = pa.BufferReader(schema_wire)
    message = pa.ipc.read_message(schema_source)
    assert message.type == "schema" and message.metadata_version == pa.ipc.MetadataVersion.V5
    assert message.body is None or message.body.size == 0
    assert pa.ipc.read_schema(message).equals(expected_schema, check_metadata=True)
    assert schema_source.tell() == len(schema_wire)

    wire = stream_path.read_bytes()
    assert wire.startswith(schema_wire) and wire.endswith(EOS)
    source = pa.BufferReader(wire)
    with pa.ipc.open_stream(source) as reader:
        assert reader.schema.equals(expected_schema, check_metadata=True)
        values = [batch.column(0).cast(pa.int64()).to_pylist() for batch in reader]
    assert values == expected_batches and source.tell() == len(wire)
    messages = list(pa.ipc.MessageReader.open_stream(wire))
    assert [message.type for message in messages] == ["schema"] + ["record batch"] * len(expected_batches)
    assert all(message.metadata_version == pa.ipc.MetadataVersion.V5 for message in messages)
    print(f"{name!r} {unit} {timezone or 'local'} nullable={nullable} "
          f"batches={list(map(len, values))} sha256={hashlib.sha256(wire).hexdigest()}")


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1"
    with tempfile.TemporaryDirectory(prefix="arrow-timestamp-native-") as temporary:
        directory = Path(temporary)
        for unit in ("s", "ms", "us", "ns"):
            for timezone in (None, "UTC"):
                check_case(directory, "時刻-é", unit, timezone, True, False)
        check_case(directory, "clock", "ns", "UTC", False, False)
        check_case(directory, "empty", "us", None, False, True)
        check_case(directory, "", "s", "UTC", True, True)


if __name__ == "__main__":
    main()
