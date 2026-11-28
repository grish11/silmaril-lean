#!/usr/bin/env python3
"""Check parsed flexible quantification and the intact LiveHourClock."""

import os
from pathlib import Path
import runpy
import subprocess
import tempfile


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
REVISION = "bc1b506bdcad80bb518bf3776a9161c34ff0fc4c"
LIVENESS = "test-model/examples/SpecifyingSystems/Liveness/"
TLCE = "src/tla2sany/StandardModules/TLCExt.tla"
TLCE_SHA256 = "6c3e7e54cf1b8a4d2d1c7a5fd088f06452edce68ec28d8be99392cc0037a5399"


def main():
    lake = os.environ.get("LAKE", "lake")
    staging = runpy.run_path(str(HERE.parent / "tla-parser" / "check.py"))
    clock = runpy.run_path(str(HERE.parent / "tla-source-acceptance" / "check.py"))
    if staging["REVISION"] != REVISION or clock["REVISION"] != REVISION:
        raise RuntimeError("review the temporal source acceptance pins")
    files = {
        path: staging["UPSTREAM"][path]
        for path in (LIVENESS + "LiveHourClock.tla", clock["HOUR_CLOCK"])
    }
    files.update({clock["NATURALS"]: clock["NATURALS_SHA256"], TLCE: TLCE_SHA256})
    subprocess.run(
        [
            lake, "build", "--wfail",
            "+Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs",
            "+Silmaril.Logic.Temporal.TLA.DataElab.Tagged.Thms",
            "+Silmaril.Logic.Temporal.TLA.DataElab.Temporal.Thms",
            "+Silmaril.Logic.Temporal.TLA.StutterReduction.Thms",
            "+Mathlib.Data.Nat.Find",
        ],
        cwd=ROOT,
        check=True,
    )
    subprocess.run(
        [lake, "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
         str(HERE / "Flexible.lean")],
        cwd=ROOT,
        check=True,
    )
    with tempfile.TemporaryDirectory(prefix="silmaril-live-hour-clock-") as temporary:
        for path, digest in files.items():
            staging["download"](
                f"{staging['RAW']}/{path}", Path(temporary) / Path(path).name, digest
            )
        subprocess.run(
            [lake, "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
             str(HERE / "LiveHourClock.lean")],
            cwd=ROOT,
            env={**os.environ, "SILMARIL_TLA_LIVE_CLOCK_FIXTURES": temporary},
            check=True,
        )


if __name__ == "__main__":
    main()
