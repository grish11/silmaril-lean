#!/usr/bin/env python3
"""Compare the raw block profile with the coverage matrix's pinned liblz4."""
from ctypes import CDLL, c_char_p, c_int, c_void_p, create_string_buffer
from hashlib import sha256
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

PIN = "ebb370ca83af193212df4dcbadcc5d87bc0de2f0"
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def require(test, label):
    if not test:
        raise SystemExit(label)


def run(*command):
    return subprocess.check_output(command, cwd=ROOT)


def build_reference(work):
    source = work / "lz4"
    run("git", "init", "-q", source)
    run("git", "-C", source, "fetch", "-q", "--depth=1", "https://github.com/lz4/lz4.git", PIN)
    run("git", "-C", source, "checkout", "-q", "--detach", "FETCH_HEAD")
    require(run("git", "-C", source, "rev-parse", "HEAD").decode().strip() == PIN, "unexpected liblz4 pin")
    library = work / "liblz4.so"
    run("cc", "-std=c99", "-O2", "-fPIC", "-shared", source / "lib/lz4.c", "-o", library)
    lib = CDLL(str(library))
    lib.LZ4_compressBound.argtypes = [c_int]
    lib.LZ4_compressBound.restype = c_int
    for function in (lib.LZ4_compress_default, lib.LZ4_decompress_safe):
        function.argtypes = [c_char_p, c_void_p, c_int, c_int]
        function.restype = c_int
    return lib


def reference_encode(lib, data):
    capacity = lib.LZ4_compressBound(len(data))
    output = create_string_buffer(capacity)
    size = lib.LZ4_compress_default(data, output, len(data), capacity)
    require(size > 0, "liblz4 could not encode fixture")
    return output.raw[:size]


def reference_decode(lib, block, capacity):
    storage = max(1, capacity)
    output = create_string_buffer(b"\xa5" * storage, storage)
    size = lib.LZ4_decompress_safe(block, output, len(block), capacity)
    return None if size < 0 else output.raw[:size]


def lean(work, mode, data, *sizes):
    source, target = work / "input.bin", work / "output.bin"
    source.write_bytes(data)
    target.unlink(missing_ok=True)
    command = ["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
               HERE / "Interop.lean", mode, source, target, *map(str, sizes)]
    run_result = subprocess.run(command, stdout=subprocess.PIPE, text=True, cwd=ROOT)
    if run_result.returncode == 3:
        return run_result.stdout.strip().rsplit(".", 1)[-1]
    run_result.check_returncode()
    return target.read_bytes()


def lean_decode(work, block, expected):
    return lean(work, "decode", block, len(block), len(block), expected, expected)


def digest(data):
    return sha256(data).hexdigest()


def check_writers(work, lib):
    inputs = {
        "empty": b"",
        "short-four": b"abcd",
        "literal-fourteen": bytes(range(14)),
        "literal-fifteen": bytes(range(15)),
        "literal-270": bytes(i % 251 for i in range(270)),
        "overlap-4096": b"a" * 4096,
        "pattern-65537": bytes(i % 251 for i in range(65537)),
    }
    for name, plain in inputs.items():
        reference = reference_encode(lib, plain)
        literal = lean(work, "encode", plain)
        require(lean_decode(work, reference, len(plain)) == plain, f"{name}: liblz4 → Lean")
        require(reference_decode(lib, literal, len(plain)) == plain, f"{name}: Lean → liblz4")
        print(f"{name}: both directions passed ({len(plain)} bytes)")
        print(f"  sha256 raw={digest(plain)} liblz4={digest(reference)} lean={digest(literal)}")


def check_wire(work, lib):
    final = b"\x50bcdef"
    literal = bytes(i % 251 for i in range(525))
    history = bytes(i % 251 for i in range(65535))
    extra = len(history) - 15
    max_offset = b"\xf3" + b"\xff" * (extra // 255) + bytes([extra % 255]) + history + b"\xff\xff" + final
    valid = {
        "at-twelve": (bytes.fromhex("13 61 01 00") + final, b"a" * 8 + b"bcdef"),
        "two-sequences": (bytes.fromhex("10 61 01 00 03 01 00") + final, b"a" * 12 + b"bcdef"),
        "final-low-nibble": (bytes.fromhex("1f 61"), b"a"),
        "literal-extension-chain": (bytes.fromhex("f0 ff ff 00") + literal, literal),
        "match-extension-zero": (bytes.fromhex("1f 61 01 00 00") + final, b"a" * 20 + b"bcdef"),
        "match-extension-chain": (bytes.fromhex("1f 61 01 00 ff 00") + final, b"a" * 275 + b"bcdef"),
        "max-offset": (max_offset, history + history[:7] + b"bcdef"),
    }
    for name, (block, plain) in valid.items():
        require(reference_decode(lib, block, len(plain)) == plain, f"{name}: liblz4 decode")
        require(lean_decode(work, block, len(plain)) == plain, f"{name}: Lean decode")
        print(f"{name}: both decoders passed, sha256 wire={digest(block)} raw={digest(plain)}")

    malformed = {
        "missing-empty-token": (b"", 0, "truncated"),
        "nonzero-empty-token": (b"\x01", 0, "invalidTail"),
        "tail-start-eleven": (bytes.fromhex("12 61 01 00") + final, 12, "invalidTail"),
        "tail-four-literals": (bytes.fromhex("14 61 01 00 40") + b"bcde", 13, "invalidTail"),
        "missing-final": (bytes.fromhex("13 61 01 00"), 8, "truncated"),
        "offset-past-history": (bytes.fromhex("13 61 02 00") + final, 13, "invalidOffset"),
        "truncated-literal-extension": (bytes.fromhex("f0 ff"), 300, "truncated"),
        "truncated-match-extension": (bytes.fromhex("1f 61 01 00 ff"), 300, "truncated"),
        "truncated-offset": (bytes.fromhex("13 61 01"), 13, "truncated"),
        "trailing-byte": (b"\x20ab\x00", 2, "truncated"),
        "output-too-small": (b"\x20ab", 1, "outputSizeMismatch"),
        "output-too-large": (b"\x20ab", 3, "outputSizeMismatch"),
    }
    for name, (block, expected, reason) in malformed.items():
        observed = reference_decode(lib, block, expected)
        require(observed is None or len(observed) != expected, f"{name}: liblz4 exact-size wrapper")
        require(lean_decode(work, block, expected) == reason, f"{name}: Lean must report {reason}")
        result = "decode rejected" if observed is None else f"decoded {len(observed)} bytes"
        print(f"{name}: Lean {reason}, liblz4 {result}, sha256 wire={digest(block)}")

    zero_offset = bytes.fromhex("13 61 00 00") + final
    require(reference_decode(lib, zero_offset, 13) == b"a" + bytes(7) + b"bcdef", "liblz4 zero-offset observation")
    require(lean_decode(work, zero_offset, 13) == "invalidOffset", "Lean must reject offset zero")
    print(f"zero-offset: Lean invalidOffset, liblz4 produced zero fill, sha256 wire={digest(zero_offset)}")


def check_bounds(work):
    checks = {
        (3, 2, 2, 2): "compressedLimit",
        (3, 3, 2, 1): "outputLimit",
        (2, 3, 2, 2): "compressedSizeMismatch",
        (4, 4, 2, 2): "compressedSizeMismatch",
    }
    for sizes, reason in checks.items():
        require(lean(work, "decode", b"\x20ab", *sizes) == reason, f"{sizes}: Lean must report {reason}")
        print(f"bounds {sizes}: Lean {reason}")


def main():
    with TemporaryDirectory(prefix="silmaril-lz4-") as directory:
        work = Path(directory)
        lib = build_reference(work)
        print(f"liblz4 v1.10.0 {PIN}")
        check_writers(work, lib)
        check_wire(work, lib)
        check_bounds(work)


if __name__ == "__main__":
    main()
