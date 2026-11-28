#!/usr/bin/env python3
"""Compare bounded RLE-profile frame execution with pinned libzstd."""
from hashlib import sha256
from pathlib import Path
from runpy import run_path
import subprocess
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
oracle = run_path(str(HERE / "check_rle.py"))
build_reference = oracle["build_reference"]
run = oracle["run"]
require = oracle["require"]
PIN = oracle["PIN"]
sequence_section = oracle["sequence_section"]
WINDOW = 1024


def raw(data):
    return 0, len(data), data


def rle(count, byte):
    return 1, count, bytes((byte,))


def compressed(reference, literals, sequence_bytes, literal_writer="raw"):
    body = run(reference, literal_writer, data=literals) + sequence_bytes
    return 2, len(body), body


def single(ll, offset_value, match):
    code = offset_value.bit_length() - 1
    return sequence_section((ll, code, match - 3), (code, 0, 0), [(offset_value - (1 << code), 0, 0)])


def frame(blocks, checksum=b""):
    descriptor = 4 if checksum else 0
    header = bytes.fromhex("28 b5 2f fd") + bytes((descriptor, 0))
    return header + b"".join(
        ((size << 3) | (kind << 1) | (i == len(blocks) - 1)).to_bytes(3, "little") + body
        for i, (kind, size, body) in enumerate(blocks)
    ) + checksum


def lean(work, encoded, *, input_cap=None, output_cap=131072, window_cap=WINDOW, command_cap=98047):
    source, output = work / "input", work / "decoded"
    source.write_bytes(encoded)
    output.unlink(missing_ok=True)
    input_cap = len(encoded) if input_cap is None else input_cap
    observed = subprocess.run(
        ["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
         HERE / "RleFrameInterop.lean", source, output, str(input_cap), str(output_cap), str(window_cap),
         str(command_cap)],
        cwd=ROOT, stdout=subprocess.PIPE, text=True,
    )
    if observed.returncode == 3:
        require(not output.exists(), "failed frame emitted an output file")
        return observed.stdout.strip()
    require(observed.returncode == 0, f"Lean fixture driver failed: {observed.stdout.strip()}")
    return output.read_bytes()


def expect_error(work, encoded, reason, **limits):
    actual = lean(work, encoded, **limits)
    require(isinstance(actual, str) and reason in actual, f"expected {reason}, got {actual!r}")


def expect_native_error(reference, encoded, capacity=131072):
    result = subprocess.run([reference, "decode", str(capacity)], input=encoded, stdout=subprocess.PIPE)
    require(result.returncode == 3, "expected libzstd rejection")


def main():
    with TemporaryDirectory(prefix="silmaril-zstd-rle-frame-") as directory:
        work = Path(directory)
        reference = build_reference(work)
        print(f"libzstd v1.5.7 {PIN}")

        mixed = [
            raw(b"abcdefghijklmno"),
            compressed(reference, b"UV!", single(2, 9, 6)),  # Insert distance 6.
            raw(b"xy"),
            rle(3, ord("M")),
            compressed(reference, b"pqrs", b"\0"),
            compressed(reference, b"", single(0, 3, 9)),  # Reuse distance 6 minus one.
            compressed(reference, b"Z" * 4, single(1, 3, 5), "rle"),
        ]
        mixed_plain = run(reference, "decode", data=frame(mixed))
        checksum = run(reference, "compress-checksum", data=mixed_plain)[-4:]
        mixed_checked = frame(mixed, checksum)
        seed = bytes(i % 251 for i in range(WINDOW))
        rolled = [raw(seed), rle(13, ord("x")), compressed(reference, b"", single(0, WINDOW + 2, 3))]
        rolled_plain = seed + b"x" * 13 + seed[14:17]
        double = sequence_section((17, 3, 36), (3, 2, 1), [(2, 1, 1), (4, 3, 0)])
        double_frame = frame([raw(b"abcdefgh"), compressed(reference, b"A" * 19 + b"B" * 18 + b"!", double)])
        double_plain = run(reference, "decode", data=double_frame)
        cases = (
            ("mixed-blocks-and-repeats", frame(mixed), mixed_plain),
            ("mixed-blocks-and-checksum", mixed_checked, mixed_plain),
            ("rolling-window", frame(rolled), rolled_plain),
            ("two-commands", double_frame, double_plain),
            ("zero-count-rle-literals", frame([compressed(reference, b"z" * 4, b"\0", "rle")]), b"zzzz"),
        )
        for name, encoded, expected in cases:
            require(run(reference, "decode", data=encoded) == expected, f"{name}: libzstd output")
            require(lean(work, encoded, output_cap=len(expected)) == expected, f"{name}: Lean output")
            print(f"{name}: both decoded, frame={sha256(encoded).hexdigest()} plain={sha256(expected).hexdigest()}")

        at_window = frame(rolled[:-1] + [compressed(reference, b"", single(0, WINDOW + 3, 3))])
        require(run(reference, "decode", data=at_window) == seed + b"x" * 13 + seed[13:16],
                "libzstd distance equal to window")
        expect_error(work, at_window, "offsetOutsideWindow")
        print(f"distance equal to window: libzstd decoded, Lean profile rejected, frame={sha256(at_window).hexdigest()}")

        repeat_modes = frame([
            compressed(reference, b"a", single(1, 1, 3)),
            compressed(reference, b"b", bytes.fromhex("01 fc 01")),
        ])
        require(run(reference, "decode", data=repeat_modes) == b"aaaabbbb", "libzstd repeat tables")
        expect_error(work, repeat_modes, "unsupportedModes 252")
        print(f"repeat tables after RLE: libzstd decoded, Lean unsupported, frame={sha256(repeat_modes).hexdigest()}")
        ordinary_plain = b"abcde" * 512
        ordinary = run(reference, "compress", data=ordinary_plain)
        require(run(reference, "decode", data=ordinary) == ordinary_plain, "libzstd ordinary frame")
        expect_error(work, ordinary, "unsupportedModes 0", window_cap=131072)
        print(f"predefined tables: libzstd decoded, Lean unsupported, frame={sha256(ordinary).hexdigest()}")

        zero_marker = frame(mixed[:-1] + [compressed(reference, b"Z" * 4, single(1, 3, 5) + b"\0")])
        rejected = (
            ("zero-final-byte", zero_marker, "badEndMarker"),
            ("truncated-block", frame(mixed)[:-1], "truncated"),
            ("truncated-checksum", mixed_checked[:-1], "truncated"),
            ("wrong-checksum", mixed_checked[:-1] + bytes((mixed_checked[-1] ^ 1,)), "checksumMismatch"),
            ("frame-suffix", mixed_checked + b"\0", "trailingInput"),
        )
        for name, encoded, reason in rejected:
            expect_native_error(reference, encoded)
            expect_error(work, encoded, reason)
            print(f"{name}: both rejected, frame={sha256(encoded).hexdigest()}")
        expect_native_error(reference, mixed_checked, len(mixed_plain) - 1)
        expect_error(work, mixed_checked, "outputLimit", output_cap=len(mixed_plain) - 1)
        expect_error(work, mixed_checked, "inputLimit", input_cap=len(mixed_checked) - 1)
        expect_error(work, mixed_checked, "windowLimit", window_cap=WINDOW - 1)
        expect_error(work, double_frame, "commandLimit", command_cap=1)
        print("output, compressed input, window and per-block command caps: Lean rejected")


if __name__ == "__main__":
    main()
