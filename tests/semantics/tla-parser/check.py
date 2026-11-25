#!/usr/bin/env python3
"""Run native syntax regressions and optionally compare against pinned SANY."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tarfile
import tempfile
from urllib.request import urlopen


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
REVISION = "bc1b506bdcad80bb518bf3776a9161c34ff0fc4c"
TLATOOLS = "tlatools/org.lamport.tlatools"
RAW = f"https://raw.githubusercontent.com/tlaplus/tlaplus/{REVISION}/{TLATOOLS}"
ARCHIVE = "2217af98440625ba2b31637620fd9d1d7b82c1fc34ee46cd79118b6e758f4d14"
UPSTREAM = {
    "test-model/examples/SpecifyingSystems/Liveness/HourClock.tla":
        "985903176db4725f9cf25df84ad84dcd53ba94be80d26298b87ec86fbc9b08b3",
    "test-model/examples/SpecifyingSystems/Liveness/LiveHourClock.tla":
        "d363d32fa6a20f7aa6b2590ba95e2a4ffd7849107423ae3bbc5ac96d10693064",
    "test-model/DieHard.tla":
        "9ca268ae443b82715c59591f2da4c81a65d0c276e7c5f2d9afb42658289f1ff9",
}
IN_PLACE = {
    "BoundedCounter.tla": "24d769ab5e0785ff4a89c93712f38786d681bd761b93cd89d8adf2cc896b8c5b",
    "BitPair.tla": "23eec77423bedfe91db1645bddc57acc46c60d4f69d37faddc5c51160640f7ec",
}


def verify(path, expected):
    with path.open("rb") as stream:
        actual = hashlib.file_digest(stream, "sha256").hexdigest()
    if actual != expected:
        raise RuntimeError(f"SHA-256 mismatch for {path}: {actual}")


def download(url, path, digest):
    with urlopen(url, timeout=60) as response, path.open("wb") as destination:
        shutil.copyfileobj(response, destination)
    verify(path, digest)


def run_sany(work, cases):
    archive = work / "tlaplus.tar.gz"
    download(f"https://codeload.github.com/tlaplus/tlaplus/tar.gz/{REVISION}", archive, ARCHIVE)
    with tarfile.open(archive) as source:
        source.extractall(work, filter="data")
    build = work / f"tlaplus-{REVISION}" / TLATOOLS
    subprocess.run(["ant", "-q", "-f", "customBuild.xml", "compile"], cwd=build, check=True)
    classes = str(build / "class")
    subprocess.run(["javac", "-cp", classes, "-d", str(work), str(HERE / "SanySyntax.java")], check=True)
    subprocess.run(["java", "-cp", os.pathsep.join([str(work), classes]), "SanySyntax", *cases], check=True)
    print(f"Pinned SANY syntax verdicts passed ({len(cases) // 2} modules)", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", action="store_true", help="include the three pinned upstream modules")
    parser.add_argument("--sany", action="store_true", help="also run the pinned syntax-only JavaCC oracle")
    parser.add_argument("--no-build", action="store_true", help="use the existing Lake build of the parser")
    args = parser.parse_args()
    lake = os.environ.get("LAKE", "lake")
    if not args.no_build:
        subprocess.run([lake, "build", "--wfail", "+Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs"],
                       cwd=ROOT, check=True)

    with tempfile.TemporaryDirectory(prefix="silmaril-tla-parser-") as temporary:
        work = Path(temporary)
        native = []
        sany = []
        for case in json.loads((HERE / "cases.json").read_text(encoding="utf-8")):
            path = work / (case["name"] + ".tla")
            source = case.get("source")
            if source is None:
                source = "---- MODULE Fixture ----\n" + case["body"] + "\n====\n"
            path.write_bytes(source.encode("utf-8"))
            native.extend([str(path), case["native"]])
            sany.extend([str(path), case.get("sany", case["native"])])
        for name, digest in IN_PLACE.items():
            path = HERE.parent / "tla-quint" / name
            verify(path, digest)
            sany.extend([str(path), "accept"])
        if args.upstream or args.sany:
            for remote, digest in UPSTREAM.items():
                path = work / Path(remote).name
                download(f"{RAW}/{remote}", path, digest)
                native.extend([str(path), "accept"])
                sany.extend([str(path), "accept"])
        subprocess.run([lake, "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                        "--run", str(HERE / "Parser.lean"), *native], cwd=ROOT, check=True)
        if args.sany:
            run_sany(work, sany)


if __name__ == "__main__":
    main()
