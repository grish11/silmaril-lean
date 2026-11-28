"""Independently compare native Arrow input to the exact Lean Parquet groups."""

import argparse
from hashlib import sha256
from importlib.metadata import version
import os
from pathlib import Path
from runpy import run_path
import subprocess
import sys

import pyarrow as pa


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
ARROW = ROOT / "scripts/arrow-mixed-named-oracle/check.py"
PARQUET = ROOT / "scripts/parquet-mixed-v1-writer-oracle/check.py"
PINS = {
    "required.arrows": "159a750c31e61edbd13715a66f6f605b205e6a3d54717a6a38fbf71798189adf",
    "mixed.parquet": "ae102b423cc69682d1279c72945a1046aa05ab28d85d1688da265c6b521d321b",
    "required.parquet": "4e28b0952c623e29988ea206c6aed95b9607488a17f5c3f714824c9136bca630",
    "empty-batch.parquet": "9c2cb4a9a24931a104e4e4edcfcd0df862d79f36036a0ddab4f7cdf0dc32ade1",
}


def pin(path):
    digest = sha256(path.read_bytes()).hexdigest()
    print(f"{digest}  {path.name}", flush=True)
    assert digest == PINS[path.name], f"{path.name}: fixture hash changed"


def observe(wire):
    with pa.BufferReader(wire) as carrier, pa.ipc.open_stream(carrier) as source:
        integer, binary = source.schema
        assert integer.type == pa.int32() and binary.type == pa.binary_view()
        fields = [(field.name, field.nullable) for field in source.schema]
        groups = []
        for batch in source:
            batch.validate(full=True)
            groups.append([column.to_pylist() for column in batch.columns])
        assert carrier.tell() == len(wire)
        assert wire.endswith(bytes.fromhex("ffffffff00000000"))
    return fields, groups


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    out = parser.parse_args().out.resolve()
    assert pa.__version__ == pa.cpp_build_info.version == "26.0.1"
    assert version("thrift") == "0.25.0"
    subprocess.run([sys.executable, str(ARROW), "--out", str(out)], cwd=ROOT, check=True)
    stream = run_path(str(ARROW))["stream"]
    required = out / "required.arrows"
    required.write_bytes(stream(pa.schema([
        pa.field("count", pa.int32(), nullable=False),
        pa.field("raw", pa.binary_view(), nullable=False),
    ]), [([-2**31, 0], [b"", b"\xff\x00\x80"]), ([2**31 - 1], [b"*" * 20])]))
    pin(required)

    subprocess.run(
        [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
         "-DwarningAsError=true", "--run", str(HERE / "Emit.lean"), str(out)],
        cwd=ROOT, check=True,
    )
    thrift = run_path(str(ROOT / "tests/formats/parquet-timestamp-leaf/check-fixtures.py"))
    parquet = run_path(str(PARQUET))
    for name, counts in (("mixed", [3, 0, 2]), ("required", [2, 1]), ("empty-batch", [0])):
        fields, groups = observe((out / f"{name}.arrows").read_bytes())
        assert [len(group[0]) for group in groups] == counts
        path = out / f"{name}.parquet"
        wire = path.read_bytes()
        parquet["check_wire_groups"](thrift, wire, fields, groups)
        parquet["check_arrow_groups"](wire, fields, groups)
        pin(path)
    print("PyArrow and Thrift agree on every original native Arrow batch and emitted Parquet group.")


if __name__ == "__main__":
    main()
