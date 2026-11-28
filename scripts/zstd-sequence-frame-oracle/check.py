#!/usr/bin/env python3
"""Whole-frame profile checks against pinned libzstd."""
from hashlib import sha256
from pathlib import Path
import random
from runpy import run_path
import subprocess
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
common = run_path(str(ROOT / "scripts/zstd-literal-oracle/check_rle_frame.py"))
payload = run_path(str(ROOT / "scripts/zstd-compressed-block-oracle/check.py"))
run, require, frame, raw, rle, compressed, single = (
    common[name] for name in ("run", "require", "frame", "raw", "rle", "compressed", "single")
)
WINDOW = common["WINDOW"]


def lean(work, encoded, *, input_cap=None, output_cap=131072, window_cap=131072, command_cap=98047):
    source, output = work / "input", work / "decoded"
    source.write_bytes(encoded)
    output.unlink(missing_ok=True)
    input_cap = len(encoded) if input_cap is None else input_cap
    result = subprocess.run(
        ["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
         HERE / "Interop.lean", source, output, str(input_cap), str(output_cap), str(window_cap),
         str(command_cap)],
        cwd=ROOT, stdout=subprocess.PIPE, text=True,
    )
    if result.returncode == 3:
        require(not output.exists(), "failed frame yielded an output file")
        return result.stdout.strip()
    result.check_returncode()
    return output.read_bytes()


def rejected(work, encoded, reason, **limits):
    actual = lean(work, encoded, **limits)
    require(isinstance(actual, str) and reason in actual, f"expected {reason}, got {actual!r}")


def main():
    with TemporaryDirectory(prefix="silmaril-zstd-sequence-frame-") as directory:
        work = Path(directory)
        native = common["build_reference"](work)
        print(f'libzstd v1.5.7 {common["PIN"]}')

        fixture = list(payload["fixture"](native))
        mixed = [block for _, block, _, _ in fixture]
        mixed_plain = b"".join(out for _, _, _, out in fixture)
        checksum = run(native, "compress-checksum", data=mixed_plain)[-4:]
        checked = frame(mixed, checksum)

        ordinary_plain = b"abcde" * 512
        ordinary = run(native, "compress-checksum", data=ordinary_plain)
        descriptor = ordinary[4]
        require(descriptor & 4 and (descriptor & 32 or descriptor >> 6),
                "ordinary compressor fixture must declare checksum and content size")
        body = run(native, "first-block", data=ordinary[:-4])
        require((body[0] & 3) in (0, 1), "ordinary compressor fixture must use raw/RLE literals")

        seed = bytes(i % 251 for i in range(WINDOW))
        history = [raw(seed), rle(13, ord("x"))]
        near_window = frame(history + [compressed(native, b"", single(0, WINDOW + 2, 3))])
        exact_window = frame(history + [compressed(native, b"", single(0, WINDOW + 3, 3))])

        for name, encoded, expected in (
            ("nine-block Repeat and history", frame(mixed), mixed_plain),
            ("nine-block checksum", checked, mixed_plain),
            ("library produced with declared size and checksum", ordinary, ordinary_plain),
            ("distance one below window", near_window, seed + b"x" * 13 + seed[14:17]),
        ):
            require(run(native, "decode", data=encoded) == expected, f"{name}: native decode")
            require(lean(work, encoded, output_cap=len(expected)) == expected, f"{name}: Lean decode")
            print(f"{name}: both decoded, frame={sha256(encoded).hexdigest()}")

        require(run(native, "decode", data=exact_window) == seed + b"x" * 13 + seed[13:16],
                "pinned libzstd accepts distance equal to the window")
        rejected(work, exact_window, "offsetOutsideWindow")
        print(f"distance equal to window: libzstd accepts, Lean rejects, "
              f"frame={sha256(exact_window).hexdigest()}")

        truncated = frame(mixed)[:-1]
        bad_size = bytes.fromhex("28 b5 2f fd 20 03 11 00 00 61 62")
        dictionary = bytes.fromhex("28 b5 2f fd 21 07 01 09 00 00 61")
        bad_marker = frame(mixed[:1] + [(2, 7, bytes.fromhex("00015400010300"))])
        for name, encoded, reason in (
            ("truncated compressed extent", truncated, "truncated"),
            ("truncated checksum", checked[:-1], "truncated"),
            ("wrong checksum", checked[:-1] + bytes([checked[-1] ^ 1]), "checksumMismatch"),
            ("incorrect content size", bad_size, "contentSizeMismatch"),
            ("trailing byte", checked + b"\x00", "trailingInput"),
            ("dictionary", dictionary, "unsupportedDictionary"),
            ("post-prefix marker failure", bad_marker, "badEndMarker"),
        ):
            rejected(work, encoded, reason)
            common["expect_native_error"](native, encoded)
            print(f"{name}: both rejected")

        rng = random.Random(8878)
        huffman_plain = bytes(65 + rng.randrange(16) for _ in range(8192))
        huffman = run(native, "compress", data=huffman_plain)
        require((run(native, "first-block", data=huffman)[0] & 3) == 2, "expected native Huffman literals")
        require(run(native, "decode", data=huffman) == huffman_plain, "native Huffman round-trip")
        rejected(work, huffman, "huffmanLiterals")
        rejected(work, frame([(2, 1, b"\x03")]), "treelessLiterals")
        rejected(work, bytes.fromhex("50 2a 4d 18 00 00 00 00"), "skippableFrame")
        rejected(work, ordinary + ordinary, "trailingInput")
        rejected(work, checked, "inputLimit", input_cap=len(checked) - 1)
        rejected(work, checked, "windowLimit", window_cap=WINDOW - 1)
        rejected(work, checked, "outputLimit", output_cap=len(mixed_plain) - 1)
        rejected(work, checked, "sequenceLimit", command_cap=0)
        print(f"Native Huffman frame classified as unsupported, frame={sha256(huffman).hexdigest()}")
        print("Lean rejected treeless literals, skippable and concatenated frames, and all four caller limits")


if __name__ == "__main__":
    main()
