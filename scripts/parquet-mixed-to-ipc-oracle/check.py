"""Check actual mixed IPC output against the pinned Parquet preparation sources."""

import argparse
from hashlib import sha256
import os
from pathlib import Path
from runpy import run_path
import subprocess
import sys

import pyarrow as pa


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SOURCE_ORACLE = ROOT / "scripts/parquet-mixed-preparation-oracle/check.py"
EOS = b"\xff" * 4 + b"\x00" * 4
OUTPUTS = ("v1.arrows", "v2.arrows", "intact-sibling.arrows", "empty-middle.arrows",
           "nullable-int32.arrows", "schema-only.arrows")


def verify_ipc(wire, table):
    schema = pa.schema([
        pa.field(table["intName"], pa.int32(), nullable=table["intNullable"]),
        pa.field(table["viewName"], pa.binary_view(), nullable=table["viewNullable"]),
    ])
    assert wire.endswith(EOS)
    with pa.BufferReader(wire) as carrier:
        with pa.ipc.open_stream(carrier) as source:
            assert source.schema == schema
            batches = list(source)
            assert carrier.tell() == len(wire)
            assert len(batches) == len(table["groups"])
            for batch, group in zip(batches, table["groups"], strict=True):
                batch.validate(full=True)
                assert batch.num_rows == group["rows"]
                assert batch.column(0).to_pylist() == group["ints"]
                assert batch.column(1).to_pylist() == [
                    None if slot is None else bytes(slot) for slot in group["bytes"]
                ]
    with pa.BufferReader(wire) as carrier:
        messages = list(pa.ipc.MessageReader.open_stream(carrier))
        assert [message.type for message in messages] == ["schema"] + ["record batch"] * len(batches)
        assert all(message.metadata_version == pa.ipc.MetadataVersion.V5 for message in messages)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", required=True, type=Path)
    out = parser.parse_args().out.resolve()
    subprocess.run([sys.executable, str(SOURCE_ORACLE), "--out", str(out)], cwd=ROOT, check=True)
    subprocess.run(
        [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
         "--run", str(HERE / "Check.lean"), str(out)],
        cwd=ROOT, check=True,
    )
    source = run_path(str(SOURCE_ORACLE))
    for name, case in zip(OUTPUTS, source["CASES"], strict=True):
        wire = (out / name).read_bytes()
        expected = source["oracle"](out, *case)
        verify_ipc(wire, expected)
        print(f"{sha256(wire).hexdigest()}  {name} (exact V5 fields, pairs, batches {case[2]} and EOS)")


if __name__ == "__main__":
    main()
