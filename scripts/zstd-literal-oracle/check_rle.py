#!/usr/bin/env python3
"""Check the RLE sequence wire profile against pinned libzstd."""
from hashlib import sha256
from pathlib import Path
from runpy import run_path
import subprocess
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
oracle = run_path(str(HERE / "check.py"))
build_reference = oracle["build_reference"]
run = oracle["run"]
require = oracle["require"]
PIN = oracle["PIN"]


def sequence_section(symbols, widths, fields):
    count = len(fields)
    encoded = bytes((count,)) if count < 128 else bytes((128 + count // 256, count % 256))
    bits = 1
    for values in fields:
        # Each tuple is in decoder order: offset, match length, literal length.
        for width, value in zip(widths, values, strict=True):
            require(0 <= value < 1 << width, "fixture extra bits exceed their field")
            bits = (bits << width) | value
    return encoded + bytes((0x54, *symbols)) + bits.to_bytes((bits.bit_length() + 7) // 8, "little")


def frame(body, history=b""):
    raw = (len(history) << 3).to_bytes(3, "little") + history if history else b""
    compressed = ((len(body) << 3) | 5).to_bytes(3, "little") + body
    return bytes.fromhex("28 b5 2f fd 00 00") + raw + compressed


def lean(work, body, history=b"", cap=98047):
    source, prior, output = (work / name for name in ("body", "history", "decoded"))
    source.write_bytes(body)
    prior.write_bytes(history)
    output.unlink(missing_ok=True)
    observed = subprocess.run(
        ["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
         HERE / "RleInterop.lean", source, prior, output, str(cap)],
        cwd=ROOT, stdout=subprocess.PIPE, text=True,
    )
    if observed.returncode == 3:
        return observed.stdout.strip()
    require(observed.returncode == 0, f"Lean fixture driver failed: {observed.stdout.strip()}")
    commands = [tuple(map(int, line.split())) for line in observed.stdout.splitlines()]
    return commands, output.read_bytes()


def expect_error(work, body, reason, history=b"", cap=98047):
    actual = lean(work, body, history, cap)
    require(isinstance(actual, str) and reason in actual, f"expected {reason}, got {actual!r}")


def main():
    with TemporaryDirectory(prefix="silmaril-zstd-rle-") as directory:
        work = Path(directory)
        reference = build_reference(work)
        print(f"libzstd v1.5.7 {PIN}")

        history = b"abcdefghijklmnopqrstuvwxyz0123456789"
        overlap = sequence_section((2, 2, 2), (2, 0, 0), [(1, 0, 0)])
        cross_byte = sequence_section((18, 5, 38), (5, 3, 1), [(2, 2, 1)])
        multiple = sequence_section((17, 3, 36), (3, 2, 1), [(2, 1, 1), (4, 3, 0)])
        many = sequence_section((0, 2, 0), (2, 0, 0), [(0, 0, 0)] * 130)
        cases = (
            ("zero-count", b"", b"literal suffix", b"\0", []),
            ("overlap", b"", b"ab!", overlap, [(2, 5, 5)]),
            ("cross-byte-fields", history, b"x" * 21 + b"!", cross_byte, [(21, 34, 53)]),
            ("two-commands", history, b"X" * 19 + b"Y" * 18 + b"!", multiple,
             [(19, 10, 44), (18, 12, 46)]),
            ("two-byte-count", b"a", b"", many, [(0, 4, 3)] * 130),
        )
        for name, prior, literals, section, expected in cases:
            body = run(reference, "raw", data=literals) + section
            encoded = frame(body, prior)
            decoded = run(reference, "decode", data=encoded)
            require(decoded.startswith(prior), f"{name}: libzstd history")
            require(lean(work, body, prior, len(expected)) == (expected, decoded[len(prior):]),
                    f"{name}: Lean commands or output")
            print(f"{name}: commands and output agreed, frame={sha256(encoded).hexdigest()} "
                  f"section={sha256(section).hexdigest()}")

        literal_section = run(reference, "raw", data=b"ab!")
        rejected = (
            ("reserved-mode-bits", bytes((1, 0x55)) + overlap[2:], "reservedModeBits"),
            ("missing-marker", overlap[:-1], "badEndMarker"),
            ("zero-final-byte", overlap + b"\0", "badEndMarker"),
            ("bit-underflow", overlap[:-1] + b"\1", "bitUnderflow"),
            ("surplus-bit", overlap[:-1] + b"\x0a", "trailingBits"),
            ("invalid-literal-symbol", overlap[:2] + b"\x24" + overlap[3:], "invalidLiteralCode"),
            ("invalid-offset-symbol", overlap[:3] + b"\x20" + overlap[4:], "invalidOffsetCode"),
            ("invalid-match-symbol", overlap[:4] + b"\x35" + overlap[5:], "invalidMatchCode"),
        )
        for name, section, reason in rejected:
            body = literal_section + section
            encoded = frame(body)
            observed = subprocess.run([reference, "decode"], input=encoded, stdout=subprocess.PIPE)
            require(observed.returncode == 3, f"{name}: libzstd expected rejection")
            expect_error(work, body, reason)
            print(f"{name}: both rejected, frame={sha256(encoded).hexdigest()}")

        ordinary_plain = b"abcde" * 512
        ordinary = run(reference, "compress", data=ordinary_plain)
        ordinary_body = run(reference, "first-block", data=ordinary)
        require(run(reference, "decode", data=ordinary) == ordinary_plain, "libzstd ordinary frame")
        expect_error(work, ordinary_body, "unsupportedModes 0")
        print(f"ordinary predefined-mode frame: libzstd decoded, Lean unsupported, frame={sha256(ordinary).hexdigest()}")
        expect_error(work, literal_section + overlap, "commandLimit", cap=0)
        print("command cap: Lean rejected")


if __name__ == "__main__":
    main()
