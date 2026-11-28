#!/usr/bin/env python3
"""Compare decoded-command execution with pinned libzstd on authored frames."""
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
WINDOW = 1024


def encode_block(literals, commands, last):
    if not commands:
        body, kind = literals, 0
    else:
        # Three RLE-mode symbol tables. Length codes 0..15 and 0..31
        # need no extra bits. Every command shares its three RLE symbols.
        ll_code, value, length = commands[0]
        offset_code = value.bit_length() - 1
        require(len(literals) < 32 and ll_code < 16 and 3 <= length <= 34, "fixture fields")
        bits = 1  # End marker. The backward reader starts with the high payload bits.
        for ll, value, ml in commands:
            require((ll, value.bit_length() - 1, ml) == (ll_code, offset_code, length),
                    "commands must share the RLE symbols")
            bits = (bits << offset_code) | (value - (1 << offset_code))
        stream = bits.to_bytes((bits.bit_length() + 7) // 8, "little")
        body = (bytes([len(literals) << 3]) + literals
                + bytes([len(commands), 0x54, ll_code, offset_code, length - 3]) + stream)
        kind = 2
    return ((len(body) << 3) | (kind << 1) | last).to_bytes(3, "little") + body


def frame(blocks):
    # No implicit content size or dictionary. Window_Descriptor 0 means 1 KiB.
    return bytes.fromhex("28 b5 2f fd 00 00") + b"".join(
        encode_block(literals, commands, i == len(blocks) - 1)
        for i, (literals, commands) in enumerate(blocks)
    )


def lean(work, blocks, capacity):
    source, output = work / "program", work / "output"
    source.write_text("".join(
        " ".join(str(field) for command in commands for field in command)
        + "|" + " ".join(map(str, literals)) + "\n"
        for literals, commands in blocks
    ), encoding="ascii")
    output.unlink(missing_ok=True)
    result = subprocess.run(
        ["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
         HERE / "SequenceInterop.lean", source, output, str(WINDOW), str(capacity)],
        cwd=ROOT, stdout=subprocess.PIPE, text=True,
    )
    if result.returncode == 3:
        return result.stdout.strip()
    result.check_returncode()
    return output.read_bytes(), tuple(map(int, result.stdout.split()))


def expect_native_error(reference, encoded, capacity):
    observed = subprocess.run([reference, "decode", str(capacity)], input=encoded, stdout=subprocess.PIPE)
    require(observed.returncode == 3, f"expected libzstd rejection, got {observed.returncode}")


def main():
    with TemporaryDirectory(prefix="silmaril-zstd-sequences-") as directory:
        work = Path(directory)
        reference = build_reference(work)
        print(f"libzstd v1.5.7 {PIN}")

        overlap = [(b"ab!", [(2, 5, 5)])]
        repeats = [
            (b"abcdefghijklmno", []),
            (b"X!", [(1, 1, 5)]),     # (1, 4, 8)
            (b"YZ", [(1, 2, 4)]),     # (4, 1, 8)
            (b"Q", [(1, 3, 6)]),      # (8, 4, 1)
            (b"raw", []),             # Retain offsets across a raw block.
            (b"?", [(0, 1, 3)]),      # (4, 8, 1)
            (b"#", [(0, 2, 5)]),      # (1, 4, 8)
            (b"uv", [(2, 9, 8)]),     # (6, 1, 4)
            (b".", [(0, 3, 11)]),     # (5, 6, 1)
        ]
        multiple = [(b"abcdefgh", []), (b"XY!", [(1, 2, 4), (1, 3, 4)])]
        near_window = [(bytes(i % 251 for i in range(WINDOW)), []), (b"", [(0, 1026, 3)])]
        accepted = (
            ("overlap-and-final-literal", overlap, (2, 1, 4)),
            ("all-repeat-transitions", repeats, (5, 6, 1)),
            ("two-commands-in-one-block", multiple, (8, 4, 1)),
            ("distance-one-below-window", near_window, (1023, 1, 4)),
        )
        for name, blocks, offsets in accepted:
            encoded = frame(blocks)
            plain = run(reference, "decode", data=encoded)
            require(lean(work, blocks, len(plain)) == (plain, offsets), f"{name}: Lean bytes or offsets")
            print(f"{name}: both decoded, frame={sha256(encoded).hexdigest()} plain={sha256(plain).hexdigest()}")

        rejected = (
            ("history-underflow", [(b"abc", []), (b"", [(0, 1, 3)])], 100, "historyUnderflow"),
            ("literal-underflow", [(b"ab", [(3, 1, 3)])], 100, "literalUnderflow"),
            ("special-repeat-resolves-to-zero", [(b"abcd", []), (b"", [(0, 3, 3)])], 100, "invalidOffset"),
            ("final-suffix-over-budget", overlap, 7, "outputLimit"),
        )
        for name, blocks, capacity, reason in rejected:
            encoded = frame(blocks)
            expect_native_error(reference, encoded, capacity)
            actual = lean(work, blocks, capacity)
            require(isinstance(actual, str) and actual.endswith(reason), f"{name}: expected {reason}, got {actual!r}")
            print(f"{name}: both rejected, frame={sha256(encoded).hexdigest()}")

        at_window = [(near_window[0][0], []), (b"", [(0, 1027, 3)])]
        encoded = frame(at_window)
        seed = near_window[0][0]
        require(run(reference, "decode", data=encoded) == seed + seed[:3],
                "pinned libzstd permits distance equal to the window")
        actual = lean(work, at_window, WINDOW + 3)
        require(isinstance(actual, str) and actual.endswith("offsetOutsideWindow"),
                "RFC profile rejects distance equal to the window")
        print(f"distance equal to window: libzstd decoded, Lean profile rejected, frame={sha256(encoded).hexdigest()}")


if __name__ == "__main__":
    main()
