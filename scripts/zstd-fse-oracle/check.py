#!/usr/bin/env python3
"""Compare every FSE state with the pinned libzstd table builder."""
from hashlib import sha256
from pathlib import Path
from runpy import run_path
import subprocess
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
oracle = run_path(str(ROOT / "scripts/zstd-literal-oracle/check.py"))
run = oracle["run"]
require = oracle["require"]
PIN = oracle["PIN"]


def main():
    with TemporaryDirectory(prefix="silmaril-zstd-fse-") as directory:
        work = Path(directory)
        oracle["build_reference"](work)
        library = work / "zstd/lib"
        native = work / "fse-reference"
        run("cc", "-std=c11", "-O2", "-I", library, HERE / "reference.c", library / "libzstd.a", "-o", native)
        print(f"libzstd v1.5.7 {PIN}")
        lean = ("lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                "--run", HERE / "Interop.lean")
        tables = (
            ("predefined-literal", ("literal",)),
            ("predefined-offset", ("offset",)),
            ("predefined-match", ("match",)),
            ("even", (5, 16, 16)),
            ("skew", (5, 30, -1, -1)),
            ("sparse", (5, 0, 15, -1, 0, 16)),
            ("all-low", (5, *([-1] * 32))),
            ("largest-table", (9, 257, 0, 253, -1, -1)),
            ("symbol-255", (5, 31, *([0] * 254), -1)),
        )
        for name, data in tables:
            args = tuple(map(str, data))
            expected = run(native, *args)
            actual = run(*lean, *args)
            require(actual == expected, f"{name}: table mismatch")
            print(f"{name}: {len(expected.splitlines()) - 1} states agreed, sha256={sha256(expected).hexdigest()}")

        rejected = (
            ((4, 8, 8), "accuracyLog"),
            ((10, 512, 512), "accuracyLog"),
            ((5, *([0] * 257)), "symbolLimit"),
            ((5, 17, -2, 15), "invalidWeight"),
            ((5, 0, 32, 0), "tooFewSymbols"),
            ((5, 16, 15), "wrongMass"),
            ((5, 16, 17), "wrongMass"),
        )
        for data, reason in rejected:
            observed = subprocess.run([*lean, *map(str, data)], cwd=ROOT, capture_output=True, text=True)
            require(observed.returncode == 3 and observed.stdout.strip().endswith(reason),
                    f"expected {reason}, got {observed.returncode} {observed.stdout!r}")
        print(f"{len(rejected)} normalized-input controls rejected in Lean")


if __name__ == "__main__":
    main()
