"""Compare original and returned IPC through genuine Lean Parquet files."""

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
FORWARD = ROOT / "scripts/arrow-mixed-ipc-to-parquet-oracle/check.py"
PINS = {
    "mixed": "faf4568226f8e0288a5c27a432c15711159d101170f87ec5805ddb9459b9b866",
    "required": "0fb3d6bd2aa895424d2cb723a0f25e84fc9f42b49a44b5a86d09b62a71441160",
    "empty-batch": "5c0b79381cefd1ca6cab338de728ca32596ddeb967865e4c1099292f8ede4a4f",
}


def messages(wire, count):
    with pa.BufferReader(wire) as carrier:
        records = list(pa.ipc.MessageReader.open_stream(carrier))
        assert [message.type for message in records] == ["schema"] + ["record batch"] * count
        assert all(message.metadata_version == pa.ipc.MetadataVersion.V5 for message in records)
        assert carrier.tell() == len(wire)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    out = parser.parse_args().out.resolve()
    assert pa.__version__ == pa.cpp_build_info.version == "26.0.1"
    subprocess.run([sys.executable, str(FORWARD), "--out", str(out)], cwd=ROOT, check=True)
    subprocess.run(
        [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
         "-DwarningAsError=true", "--run", str(HERE / "Return.lean"), str(out)],
        cwd=ROOT, check=True,
    )
    observe = run_path(str(FORWARD))["observe"]
    for name, counts in (("mixed", [3, 0, 2]), ("required", [2, 1]), ("empty-batch", [0])):
        source = (out / f"{name}.arrows").read_bytes()
        path = out / f"{name}-returned.arrows"
        wire = path.read_bytes()
        fields, groups = observe(source)
        assert [len(group[0]) for group in groups] == counts
        assert observe(wire) == (fields, groups)
        messages(source, len(groups))
        messages(wire, len(groups))
        digest = sha256(wire).hexdigest()
        print(f"{digest}  {path.name} {counts}")
        assert digest == PINS[name], f"{path.name}: returned carrier hash changed"
    print("PyArrow compared both carriers through exact EOS on all three round trips.")


if __name__ == "__main__":
    main()
