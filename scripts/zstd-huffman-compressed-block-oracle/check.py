#!/usr/bin/env python3
"""Replay two exact compressed bodies against pinned libzstd block output."""
import argparse
from hashlib import sha256
from io import BytesIO
import json
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

PIN = "f8745da6ff1ad1e7bab384bd1f9d742439278e99"
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
LITERALS_ORACLE = HERE.with_name("zstd-huffman-literal-state-oracle")


def run(*args, data=None):
    return subprocess.check_output(args, cwd=ROOT, input=data)


def require(condition, message):
    if not condition:
        raise SystemExit(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--zstd-source", type=Path, help="optional clean checkout at the pinned SHA")
    args = parser.parse_args()
    with TemporaryDirectory(prefix="silmaril-zstd-huffman-block-") as directory:
        work = Path(directory)
        source = args.zstd_source.resolve() if args.zstd_source else work / "zstd"
        if args.zstd_source is None:
            run("git", "init", "-q", source)
            run("git", "-C", source, "fetch", "-q", "--depth=1", "https://github.com/facebook/zstd.git", PIN)
            run("git", "-C", source, "checkout", "-q", "--detach", "FETCH_HEAD")
        # Reuse the existing frame generator, pin check and literal-state controls.
        run("python3", "-I", LITERALS_ORACLE / "check.py", "--zstd-source", source, "--out", work)
        fixture = json.loads((work / "fixture.json").read_text())
        frame = (work / "same-frame.zst").read_bytes()

        library = source / "lib"
        reference = work / "reference"
        run("cc", "-std=c11", "-Wall", "-Wextra", "-Werror", "-O2", "-I", library,
            HERE / "reference.c", library / "libzstd.a", "-o", reference)
        native = BytesIO(run(reference, data=frame))
        header, dictionary, window, maximum, total = map(int, native.readline().split())
        require((header, dictionary, window, maximum, total) == (9, 0, 135168, 131072, 135168),
                "native frame limits changed")

        first = fixture["blocks"][0]
        marker = first["block_header_offset"] + 3 + first["block_body_bytes"] - 1
        require(frame[marker] != 0, "first sequence stream marker is already zero")
        corrupt = frame[:marker] + b"\x00" + frame[marker + 1:]
        rejected = subprocess.run([reference], input=corrupt, capture_output=True, cwd=ROOT)
        require(rejected.returncode == 3, "native decoder accepted the zero sequence marker")

        paths = []
        for block, output_count in zip(fixture["blocks"], (131072, 4096), strict=True):
            offset, size, decoded = map(int, native.readline().split())
            require((offset, size, decoded) ==
                    (block["block_header_offset"], block["block_body_bytes"], output_count),
                    "native block boundaries changed")
            path = work / f'block-{block["block_index"]}.bin'
            path.write_bytes(frame[offset + 3:offset + 3 + size])
            paths.append(path)
        expected = native.read()
        require(sha256(expected).hexdigest() == fixture["input_sha256"], "native output differs from input")

        print(f'libzstd {PIN}; frame SHA-256 {fixture["frame_sha256"]}', flush=True)
        report = run("lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                     "--run", HERE / "Interop.lean", str(window), *paths, work)
        print(report.decode(), end="")
        cursor = 0
        for index, count in enumerate((131072, 4096), 1):
            actual = (work / f"block-{index}.lean.bin").read_bytes()
            require(actual == expected[cursor:cursor + count], f"block {index}: Lean and libzstd differ")
            print(f"block {index}: {count} bytes matched, SHA-256 {sha256(actual).hexdigest()}")
            cursor += count


if __name__ == "__main__":
    main()
