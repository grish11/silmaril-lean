#!/usr/bin/env python3
"""Check literal-only compressed block bodies using pinned libzstd."""
from hashlib import sha256
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

PIN = "f8745da6ff1ad1e7bab384bd1f9d742439278e99"
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
MAX_BLOCK = 131072


def require(condition, message):
    if not condition:
        raise SystemExit(message)


def run(*command, data=None):
    return subprocess.check_output(command, cwd=ROOT, input=data)


def build_reference(work):
    source = work / "zstd"
    run("git", "init", "-q", source)
    run("git", "-C", source, "fetch", "-q", "--depth=1", "https://github.com/facebook/zstd.git", PIN)
    run("git", "-C", source, "checkout", "-q", "--detach", "FETCH_HEAD")
    require(run("git", "-C", source, "rev-parse", "HEAD").decode().strip() == PIN, "unexpected libzstd revision")
    run("make", "-C", source / "lib", "-j2", "libzstd.a")
    reference = work / "reference"
    run("c++", "-std=c++11", "-O2", "-I", source / "lib", HERE / "reference.cc",
        source / "lib/libzstd.a", "-o", reference)
    return reference


def frame(body):
    header = ((len(body) << 3) | 5).to_bytes(3, "little")
    # No frame content size or dictionary, 128 KiB window, one last type-2 block.
    return bytes.fromhex("28 b5 2f fd 00 38") + header + body


def lean(work, body, limit=MAX_BLOCK, window=MAX_BLOCK):
    path, output = work / "input.bin", work / "output.bin"
    path.write_bytes(body)
    output.unlink(missing_ok=True)
    result = subprocess.run(
        ["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
         HERE / "Interop.lean", path, output, str(window), str(limit)],
        cwd=ROOT, stdout=subprocess.PIPE, text=True,
    )
    if result.returncode == 3:
        return result.stdout.strip()
    result.check_returncode()
    return output.read_bytes()


def main():
    with TemporaryDirectory(prefix="silmaril-zstd-literal-") as directory:
        work = Path(directory)
        reference = build_reference(work)
        print(f"libzstd v1.5.7 {PIN}")
        inputs = [(f"raw-{n}", "raw", bytes(i % 251 for i in range(n))) for n in (0, 31, 32, 4095, 4096)]
        inputs += [(f"rle-{n}", "rle", b"a" * n) for n in (31, 32, 4096, MAX_BLOCK)]
        cases = []
        for name, mode, plain in inputs:
            cases.append((name, run(reference, mode, data=plain) + b"\0", plain))
        cases += [
            ("wide-short-value", bytes.fromhex("1c 00 00 61 00"), b"a"),
            ("two-byte-zero-sequences", bytes.fromhex("08 61 80 00"), b"a"),
        ]
        for name, body, output in cases:
            require(run(reference, "decode", data=frame(body)) == output, f"{name}: libzstd output")
            require(lean(work, body, len(output)) == output, f"{name}: Lean output")
            print(f"{name}: both decoders passed, body={sha256(body).hexdigest()} plain={sha256(output).hexdigest()}")

        ordinary = b"abcde" * 512
        compressed = run(reference, "compress", data=ordinary)
        body = run(reference, "first-block", data=compressed)
        require(run(reference, "decode", data=compressed) == ordinary, "ordinary frame must decode in libzstd")
        require("sequences" in lean(work, body), "ordinary sequence-bearing block should remain unsupported")
        print(f"ordinary compressed frame: Lean unsupported sequences, libzstd passed, body={sha256(body).hexdigest()}")

        rejected = [
            ("absent-sequence-count", bytes.fromhex("11 61"), 2, "truncated"),
            ("trailing-sequence-byte", bytes.fromhex("11 61 00 01"), 2, "trailingSequences"),
            ("truncated-long-header", bytes.fromhex("0d 00"), 4096, "truncated"),
            ("truncated-raw-literals", bytes.fromhex("18 61 62"), 3, "truncated"),
            ("output-limit", bytes.fromhex("11 61 00"), 1, "outputLimit"),
        ]
        for name, body, limit, reason in rejected:
            observed = subprocess.run([reference, "decode", str(limit)], input=frame(body),
                                      stdout=subprocess.PIPE, cwd=ROOT)
            require(observed.returncode == 3, f"{name}: expected libzstd rejection")
            require(lean(work, body, limit).endswith(reason), f"{name}: expected Lean {reason}")
            print(f"{name}: both rejected, body={sha256(body).hexdigest()}")
        require(lean(work, bytes.fromhex("11 61 00"), 2, 2).endswith("blockLimit"), "Lean compressed bound")
        print("compressed block limit: Lean rejected overlarge extent")


if __name__ == "__main__":
    main()
