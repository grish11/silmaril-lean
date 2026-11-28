#!/usr/bin/env python3
"""Check direct and instantiated Coherence from the pinned WriteThroughCache source."""

import os
from pathlib import Path
import runpy
import subprocess
import tempfile


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
REVISION = "bc1b506bdcad80bb518bf3776a9161c34ff0fc4c"
SOURCE = "test-model/examples/SpecifyingSystems/CachingMemory/WriteThroughCache.tla"


def main():
    lake = os.environ.get("LAKE", "lake")
    staging = runpy.run_path(str(HERE.parent / "tla-parser" / "check.py"))
    if staging["REVISION"] != REVISION:
        raise RuntimeError("review the WriteThroughCache pin after the parser fixture revision change")
    subprocess.run(
        [lake, "build", "--wfail", "+Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs",
         "+Silmaril.Logic.Temporal.TLA.DataElab.Instances.Defs"],
        cwd=ROOT,
        check=True,
    )
    with tempfile.TemporaryDirectory(prefix="silmaril-write-through-") as directory:
        path = Path(directory) / "WriteThroughCache.tla"
        staging["download"](f"{staging['RAW']}/{SOURCE}", path, staging["UPSTREAM"][SOURCE])
        subprocess.run(
            [lake, "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
             str(HERE / "WriteThroughCache.lean"), str(path)],
            cwd=ROOT,
            check=True,
        )


if __name__ == "__main__":
    main()
