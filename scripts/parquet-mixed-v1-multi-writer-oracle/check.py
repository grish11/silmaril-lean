"""Check indexed groups of original Lean Parquet files and pin single-group compatibility."""

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
SINGLE = ROOT / "scripts/parquet-mixed-v1-writer-oracle/check.py"
PINS = {
    "required": "73fde01f67a8d8b97afc4744399e68cd14a0fd8b3ed9adef8791b9bc50edaa5f",
    "empty-middle": "81f6a51b3b3a033a70eaba0fbc3d9223f12aba2bde5b6b6f2f5acbb24475ac8a",
    "long-group-list": "3e39b4435846d93c9588a6115a82a61ff7d7f1d9c12cbbc44ef211d1c677276e",
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    out = parser.parse_args().out.resolve()
    assert pa.__version__ == pa.cpp_build_info.version == "26.0.1"
    assert version("thrift") == "0.25.0"
    subprocess.run([sys.executable, str(SINGLE), "--out", str(out / "single")], cwd=ROOT, check=True)
    subprocess.run(
        [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
         "-DwarningAsError=true", "--run", str(HERE / "Write.lean"), str(out)],
        cwd=ROOT, check=True,
    )
    helpers = run_path(str(SINGLE))
    thrift = run_path(str(ROOT / "tests/formats/parquet-timestamp-leaf/check-fixtures.py"))
    raw, long = helpers["RAW"], helpers["LONG"]
    many_groups = [
        ([], []) if i == 7 else ([i - 8], [None if i % 3 == 0 else bytes([i, 0, 255])])
        for i in range(16)
    ]
    cases = {
        "required": ([("id", False), ("raw", False)], [([-2**31, 0], [raw, b""]), ([2**31 - 1], [long])]),
        "empty-middle": ([("count", True), ("clé", True)], [([-7], [None]), ([], []), ([None, 0], [b"", raw])]),
        "long-group-list": ([("ordinal", False), ("payload", True)], many_groups),
    }
    for name, (fields, groups) in cases.items():
        path = out / f"{name}.parquet"
        wire = path.read_bytes()
        helpers["check_wire_groups"](thrift, wire, fields, groups)
        helpers["check_arrow_groups"](wire, fields, groups)
        digest = sha256(wire).hexdigest()
        print(f"{digest}  {path.name} {[len(ints) for ints, _ in groups]}")
        assert digest == PINS[name], f"{path.name}: fixture hash changed"
    assert (out / "singleton.parquet").read_bytes() == (out / "single/mixed.parquet").read_bytes()
    print("Pinned PyArrow and Thrift verified every ordinal in three native multi-group files.")


if __name__ == "__main__":
    main()
