#!/usr/bin/env python3
"""Compare the checked Zstandard frame profile with pinned libzstd."""
from hashlib import sha256
from pathlib import Path
from runpy import run_path
import subprocess
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
literal_oracle = run_path(str(HERE / "check.py"))
build_reference = literal_oracle["build_reference"]
run = literal_oracle["run"]
require = literal_oracle["require"]
PIN = literal_oracle["PIN"]
MAX_BLOCK = literal_oracle["MAX_BLOCK"]
ROOT = HERE.parents[1]
MAGIC = bytes.fromhex("28 b5 2f fd")


def block(kind, size, body, last=False):
    return ((size << 3) | (kind << 1) | last).to_bytes(3, "little") + body


def frame(*blocks, checksum=b""):
    descriptor = 4 if checksum else 0
    # Unknown content size, no dictionary, 1 KiB window.
    return MAGIC + bytes((descriptor, 0)) + b"".join(blocks) + checksum


def lean(work, data, max_input=None, max_output=MAX_BLOCK, max_window=MAX_BLOCK):
    source, output = work / "input.bin", work / "output.bin"
    source.write_bytes(data)
    output.unlink(missing_ok=True)
    max_input = len(data) if max_input is None else max_input
    observed = subprocess.run(
        ["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
         HERE / "FrameInterop.lean", source, output, str(max_input), str(max_output), str(max_window)],
        cwd=ROOT, stdout=subprocess.PIPE, text=True,
    )
    if observed.returncode == 3:
        return observed.stdout.strip()
    observed.check_returncode()
    return output.read_bytes()


def expect_error(work, data, reason, **limits):
    actual = lean(work, data, **limits)
    require(isinstance(actual, str) and reason in actual, f"expected Lean {reason}, got {actual!r}")


def expect_native_error(reference, data, capacity=MAX_BLOCK):
    observed = subprocess.run([reference, "decode", str(capacity)], input=data, stdout=subprocess.PIPE)
    require(observed.returncode == 3, f"expected libzstd rejection, got {observed.returncode}")


def main():
    with TemporaryDirectory(prefix="silmaril-zstd-frame-") as directory:
        work = Path(directory)
        reference = build_reference(work)
        print(f"libzstd v1.5.7 {PIN}")

        empty = run(reference, "compress", data=b"")
        raw = b"raw data"
        raw_native = run(reference, "compress", data=raw)
        checksummed = run(reference, "compress-checksum", data=raw)
        require(raw_native[4:9] == bytes((0x20, len(raw), 8 * len(raw) + 1, 0, 0)),
                "expected a single-segment raw libzstd frame")
        require(checksummed[4:9] == bytes((0x24, len(raw), 8 * len(raw) + 1, 0, 0)),
                "expected a single-segment raw libzstd frame with checksum")

        raw_literals = run(reference, "raw", data=b"de") + b"\0"
        rle_literals = run(reference, "rle", data=b"fff") + b"\0"
        mixed_plain = b"abccdefff"
        mixed_blocks = (
            block(0, 2, b"ab"),
            block(1, 2, b"c"),
            block(2, len(raw_literals), raw_literals),
            block(2, len(rle_literals), rle_literals, last=True),
        )
        mixed = frame(*mixed_blocks)
        mixed_checksum = run(reference, "compress-checksum", data=mixed_plain)[-4:]
        mixed_checked = frame(*mixed_blocks, checksum=mixed_checksum)
        window_boundary = frame(block(1, 1024, b"a", last=True))
        empty_tail = frame(block(1, 2, b"a"), block(0, 0, b"", last=True))
        cases = (
            ("native-empty", empty, b""),
            ("native-raw", raw_native, raw),
            ("native-checksum", checksummed, raw),
            ("mixed-blocks", mixed, mixed_plain),
            ("mixed-checksum", mixed_checked, mixed_plain),
            ("window-block-boundary", window_boundary, b"a" * 1024),
            ("zero-output-final-block", empty_tail, b"aa"),
        )
        for name, encoded, plain in cases:
            require(run(reference, "decode", data=encoded) == plain, f"{name}: libzstd output")
            require(lean(work, encoded, max_output=len(plain)) == plain, f"{name}: Lean output")
            print(f"{name}: both decoded, frame={sha256(encoded).hexdigest()} plain={sha256(plain).hexdigest()}")

        wrong_size = raw_native[:5] + bytes((len(raw) + 1,)) + raw_native[6:]
        extra_sequence = rle_literals + b"\0"
        dictionary = MAGIC + bytes((0x21, 7, len(raw))) + raw_native[6:]
        rejected = (
            ("truncated-raw", raw_native[:-1], "truncated"),
            ("truncated-type-2", mixed[:-1], "truncated"),
            ("unterminated-blocks", frame(block(0, 2, b"ab")), "truncated"),
            ("trailing-sequence-byte", frame(block(2, len(extra_sequence), extra_sequence, last=True)),
             "trailingSequences"),
            ("reserved-block", frame(block(3, 0, b"", last=True)), "reservedBlock"),
            ("wrong-content-size", wrong_size, "contentSizeMismatch"),
            ("truncated-checksum", mixed_checked[:-1], "truncated"),
            ("wrong-checksum", mixed_checked[:-1] + bytes((mixed_checked[-1] ^ 1,)), "checksumMismatch"),
            ("frame-suffix", mixed_checked + b"\0", "trailingInput"),
            ("nonzero-dictionary-id", dictionary, "unsupportedDictionary 7"),
        )
        for name, encoded, reason in rejected:
            expect_native_error(reference, encoded)
            expect_error(work, encoded, reason)
            print(f"{name}: both rejected, frame={sha256(encoded).hexdigest()}")

        ordinary_plain = b"abcde" * 512
        ordinary = run(reference, "compress", data=ordinary_plain)
        run(reference, "first-block", data=ordinary)  # Confirms a single last type-2 block.
        require(run(reference, "decode", data=ordinary) == ordinary_plain, "libzstd ordinary output")
        expect_error(work, ordinary, "sequences")
        print(f"sequence-bearing frame: libzstd decoded, Lean unsupported, frame={sha256(ordinary).hexdigest()}")

        combined = raw_native + mixed_checked
        require(run(reference, "decode", data=combined) == raw + mixed_plain, "libzstd concatenated output")
        expect_error(work, combined, "trailingInput")
        skippable = bytes.fromhex("50 2a 4d 18 01 00 00 00 61")
        require(run(reference, "decode", data=skippable) == b"", "libzstd skippable output")
        expect_error(work, skippable, "badMagic")
        print("concatenated and skippable frames: libzstd decoded, Lean rejected the profile")

        expect_native_error(reference, mixed, len(mixed_plain) - 1)
        expect_error(work, mixed, "outputLimit", max_output=len(mixed_plain) - 1)
        expect_error(work, mixed, "inputLimit", max_input=len(mixed) - 1)
        expect_error(work, mixed, "windowLimit", max_window=1023)
        expect_error(work, frame(block(1, 1025, b"a", last=True)), "blockLimit")
        print("output, input, window and block ceilings: Lean rejected")


if __name__ == "__main__":
    main()
