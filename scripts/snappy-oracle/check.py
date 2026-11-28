#!/usr/bin/env python3
"""Check the raw codec against the Snappy revision pinned by the coverage matrix."""

import hashlib
from pathlib import Path
import subprocess
import tempfile

PIN = "6af9287fbdb913f0794d0148c6aa43b58e63c8e3"
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def run(*command, data=None):
    return subprocess.run(command, input=data, stdout=subprocess.PIPE, check=True, cwd=ROOT).stdout


def build_reference(work):
    source, build = work / "source", work / "build"
    run("git", "init", "-q", source)
    run("git", "-C", source, "fetch", "-q", "--depth=1", "https://github.com/google/snappy.git", PIN)
    run("git", "-C", source, "checkout", "-q", "--detach", "FETCH_HEAD")
    if run("git", "-C", source, "rev-parse", "HEAD").decode().strip() != PIN:
        raise SystemExit("unexpected Snappy revision")

    run("cmake", "-S", source, "-B", build, "-DCMAKE_BUILD_TYPE=Release",
        "-DSNAPPY_BUILD_TESTS=OFF", "-DSNAPPY_BUILD_BENCHMARKS=OFF", "-DSNAPPY_INSTALL=OFF")
    run("cmake", "--build", build, "--parallel", "2")
    reference = work / "reference"
    run("c++", "-std=c++11", "-O2", "-I", source, "-I", build, HERE / "reference.cc",
        build / "libsnappy.a", "-o", reference)
    return reference


def lean(work, mode, data):
    source, target = work / "input.bin", work / "output.bin"
    source.write_bytes(data)
    run("lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
        HERE / "Interop.lean", mode, source, target)
    return target.read_bytes()


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    payloads = {
        "empty": b"",
        "literal-60": bytes(range(60)),
        "literal-61": bytes(range(61)),
        "binary-80": bytes(range(80)),
        "repeat-70": b"a" * 70,
        "pattern-100": b"abcde" * 20,
        "preamble-127": bytes(range(127)),
        "preamble-128": bytes(range(128)),
        "literal-257": bytes(range(256)) + b"\x00",
        "literal-65537": bytes(i % 251 for i in range(65537)),
    }
    with tempfile.TemporaryDirectory(prefix="silmaril-snappy-") as directory:
        work = Path(directory)
        reference = build_reference(work)
        print(f"Snappy 1.2.2 {PIN}")
        for name, payload in payloads.items():
            reference_block = run(reference, "encode", data=payload)
            lean_block = lean(work, "encode", payload)
            if lean(work, "decode", reference_block) != payload:
                raise SystemExit(f"{name}: Silmaril could not read the reference output")
            if run(reference, "decode", data=lean_block) != payload:
                raise SystemExit(f"{name}: reference could not read the Silmaril output")
            print(f"{name}: {len(payload)} bytes, both directions passed")
            print(f"  sha256 raw={digest(payload)} google={digest(reference_block)} silmaril={digest(lean_block)}")

        # The pinned encoder need not emit every width the raw reader accepts.
        binary = bytes(range(256))
        controls = {
            "overlap-copy4": (bytes.fromhex("08 04 61 62 17 02 00 00 00"), b"abababab"),
            "high-offset-copy1": (bytes.fromhex("84 02 f0 ff") + binary + bytes.fromhex("21 00"),
                                  binary + bytes(range(4))),
            "nonminimal-preamble": (bytes.fromhex("80 00"), b""),
            "nonminimal-literal-length4": (bytes.fromhex("01 fc 00 00 00 00 2a"), b"*"),
        }
        for name, (block, output) in controls.items():
            if run(reference, "decode", data=block) != output or lean(work, "decode", block) != output:
                raise SystemExit(f"{name}: disagreement on valid raw bytes")
            print(f"{name}: both decoders passed, sha256 block={digest(block)} raw={digest(output)}")


if __name__ == "__main__":
    main()
