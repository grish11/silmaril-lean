"""Compare native BinaryView IPC output with the pinned Parquet inputs."""

import argparse
from dataclasses import dataclass
from hashlib import sha256
import json
import os
from pathlib import Path
import platform
from shutil import copyfile
import subprocess
import sys

import pyarrow as pa
import pyarrow.parquet as pq

from zero_group import write_zero_cases


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
EOS = b"\xff" * 4 + b"\x00" * 4


@dataclass(frozen=True)
class Case:
    parquet: str
    ipc: str
    field: str
    nullable: bool
    rows: tuple[int, ...]


CASES = (
    Case("selected.parquet", "optional-v2.arrows", "blob", True, (4, 4)),
    Case("plain-byte-array-v1.parquet", "required-v1.arrows", "key", False, (12, 12, 12)),
    Case("schema-only.parquet", "schema-only.arrows", "blob", True, ()),
    Case("framed-zero-row-group.parquet", "empty-batch.arrows", "blob", True, (0,)),
)


def verify_pins(fixtures):
    manifest = json.loads((HERE / "sha256.json").read_text(encoding="utf-8"))
    for name, digest in manifest.items():
        assert sha256((fixtures / name).read_bytes()).hexdigest() == digest, name
    print(f"{len(manifest)} Parquet input hashes match")


def expected_groups(fixtures, case):
    with pq.ParquetFile(fixtures / case.parquet) as source:
        assert source.schema_arrow.field(case.field) == pa.field(
            case.field, pa.binary(), nullable=case.nullable
        ), case.parquet
        groups = [
            source.read_row_group(index, columns=[case.field]).column(0).to_pylist()
            for index in range(source.num_row_groups)
        ]
    assert tuple(map(len, groups)) == case.rows, case.parquet
    return groups


def verify_wire(wire, case, expected):
    assert wire.endswith(EOS), f"{case.ipc}: missing explicit EOS"
    observed_schema = pa.schema([pa.field(case.field, pa.binary_view(), nullable=case.nullable)])
    with pa.BufferReader(wire) as input_bytes:
        with pa.ipc.open_stream(input_bytes) as stream:
            assert stream.schema == observed_schema, f"{case.ipc}: wrong descriptor"
            batches = list(stream)
            assert input_bytes.tell() == len(wire), f"{case.ipc}: trailing bytes after EOS"
            assert tuple(batch.num_rows for batch in batches) == case.rows, f"{case.ipc}: wrong batch shape"
            for batch in batches:
                batch.validate(full=True)
            assert [batch.column(0).to_pylist() for batch in batches] == expected, (
                f"{case.ipc}: wrong ordered nullable octets"
            )

    with pa.BufferReader(wire) as input_bytes:
        messages = list(pa.ipc.MessageReader.open_stream(input_bytes))
        assert [msg.type for msg in messages] == ["schema"] + ["record batch"] * len(case.rows), (
            f"{case.ipc}: unexpected wire messages"
        )
        assert all(msg.metadata_version == pa.ipc.MetadataVersion.V5 for msg in messages), (
            f"{case.ipc}: wrong IPC metadata version"
        )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1"
    out = args.out.resolve()
    subprocess.run(
        [sys.executable, str(ROOT / "scripts/binary-file-observation-oracle/check.py"), "--out", str(out)],
        cwd=ROOT, check=True,
    )
    copyfile(ROOT / "data/parquet-plain-byte-array-file/plain-byte-array-v1.parquet",
             out / "plain-byte-array-v1.parquet")
    write_zero_cases(out)
    verify_pins(out)
    subprocess.run(
        [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
         "--run", str(HERE / "Check.lean"), str(out)],
        cwd=ROOT, check=True,
    )
    for case in CASES:
        wire = (out / case.ipc).read_bytes()
        verify_wire(wire, case, expected_groups(out, case))
        print(f"{sha256(wire).hexdigest()}  {case.ipc} (exact V5, batches {list(case.rows)}, EOS)")


if __name__ == "__main__":
    main()
