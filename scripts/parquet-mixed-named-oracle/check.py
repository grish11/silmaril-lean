"""Compare inserted Lean rows with independent reads of pinned Parquet inputs."""

import argparse
import json
import os
from pathlib import Path
from runpy import run_path
import subprocess
import sys


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SOURCE = ROOT / "scripts/parquet-mixed-preparation-oracle/check.py"


def flatten(table):
    return {key: value for key, value in table.items() if key != "groups"} | {
        "counts": [group["rows"] for group in table["groups"]],
        "rows": [list(pair) for group in table["groups"]
                 for pair in zip(group["ints"], group["bytes"], strict=True)],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", required=True, type=Path)
    out = parser.parse_args().out.resolve()
    subprocess.run([sys.executable, str(SOURCE), "--out", str(out)], cwd=ROOT, check=True)
    result = subprocess.check_output(
        [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
         "-DwarningAsError=true", "--run", str(HERE / "Check.lean"), str(out)],
        cwd=ROOT, text=True,
    )
    source = run_path(str(SOURCE))
    expected = [flatten(source["oracle"](out, *case)) for case in source["CASES"]]
    assert json.loads(result) == expected
    print("Six PyArrow comparisons of exact stored fields, flattened rows and source batch counts.")
    print("Six typed failure controls and one success at the exact IPC byte cap.")


if __name__ == "__main__":
    main()
