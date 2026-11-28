"""Check the actual Lean Parquet intermediate and Arrow stream from pinned inputs."""

from hashlib import sha256
from importlib.metadata import version
import os
from pathlib import Path
import platform
import runpy
import subprocess
import tempfile

import pyarrow as pa

ROOT = Path(__file__).resolve().parents[2]
SOURCE = runpy.run_path(str(ROOT / "scripts/arrow-timestamp-to-parquet-oracle/check.py"))
EOS = bytes.fromhex("ffffffff00000000")


def observe(wire):
    source = pa.BufferReader(wire)
    with pa.ipc.open_stream(source) as reader:
        assert len(reader.schema) == 1
        field = reader.schema.field(0)
        batches = [batch.column(0).cast(pa.int64()).to_pylist() for batch in reader]
    assert source.tell() == len(wire) and wire.endswith(EOS)
    return field, batches


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    fixtures = dict(SOURCE["cases"]())
    pin = sha256(b"".join(len(wire).to_bytes(8, "little") + wire for wire in fixtures.values())).hexdigest()
    assert pin == SOURCE["PIN"]
    print(f"IPC fixture-set SHA-256 {pin}", flush=True)
    with tempfile.TemporaryDirectory(prefix="arrow-timestamp-roundtrip-") as temporary:
        directory = Path(temporary)
        for name, wire in fixtures.items():
            (directory / (name + ".arrows")).write_bytes(wire)
        emitter = Path(__file__).with_name("Emit.lean")
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", "--run", str(emitter), str(directory)], cwd=ROOT, check=True)
        expected = {"ms_local", "ms_utc", "us_local", "us_utc", "ns_local", "ns_utc", "schema_only"}
        assert {file.stem for file in directory.glob("*.parquet")} == expected
        assert {file.stem for file in directory.glob("*.roundtrip")} == expected
        for name in sorted(expected):
            original = fixtures[name]
            SOURCE["verify"](original, (directory / (name + ".parquet")).read_bytes())
            output = (directory / (name + ".roundtrip")).read_bytes()
            src_field, src_batches = observe(original)
            dst_field, dst_batches = observe(output)
            assert dst_field.equals(src_field, check_metadata=True) and dst_batches == src_batches
            print(f"{name}: Arrow batch sizes {list(map(len, dst_batches))}, sha256={sha256(output).hexdigest()}")


if __name__ == "__main__":
    main()
