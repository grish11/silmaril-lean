#!/usr/bin/env python3
"""Check exact jump-table splits and all four literal streams with libzstd."""
from hashlib import sha256
from pathlib import Path
from runpy import run_path
import subprocess
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
direct = run_path(str(ROOT / "scripts/zstd-huffman-direct-oracle/check.py"))
run, require, samples = (direct[name] for name in ("run", "require", "samples"))
oracle = direct["oracle"]


def lean(work, data, mode, declared, count, input_cap=131072, output_cap=131072):
    source, destination = work / "source", work / "decoded"
    source.write_bytes(data)
    destination.unlink(missing_ok=True)
    observed = subprocess.run(
        ["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
         HERE / "Interop.lean", source, destination, mode, str(declared), str(count),
         str(input_cap), str(output_cap)],
        cwd=ROOT, stdout=subprocess.PIPE,
    )
    if observed.returncode == 3:
        require(not destination.exists(), "failed decode returned bytes")
        return observed.stdout.decode().strip()
    observed.check_returncode()
    return observed.stdout if mode == "split" else destination.read_bytes()


def payload(frames, data, native_format):
    body = run(frames, "first-block", data=data)
    require((body[0] & 3) == 2, "fresh Huffman literal section")
    size_format = (body[0] >> 2) & 3
    require(size_format == native_format, "unexpected four-stream size format")
    header_size, width = ((3, 10), (4, 14), (5, 18))[size_format - 1]
    header = int.from_bytes(body[:header_size], "little")
    regenerated, compressed = (header >> 4) & ((1 << width) - 1), header >> (4 + width)
    require(header_size + compressed < len(body), "literal section must leave sequence bytes")
    raw = body[header_size:header_size + compressed]
    require(raw[0] >= 128, "expected a direct weight description")
    tree_bytes = 1 + (raw[0] - 127 + 1) // 2
    return raw, raw[tree_bytes:], regenerated


def check_split(work, stream_bytes, count):
    lengths = [int.from_bytes(stream_bytes[i:i + 2], "little") for i in (0, 2, 4)]
    lengths.append(len(stream_bytes) - 6 - sum(lengths))
    quota = (count + 3) // 4
    counts = [quota] * 3 + [count - 3 * quota]
    expected = "".join(f"{length} {n}\n" for length, n in zip(lengths, counts)).encode()
    require(lean(work, stream_bytes, "split", len(stream_bytes), count) == expected,
            "declared and inferred extents or counts differ")
    return lengths, counts


def main():
    with TemporaryDirectory(prefix="silmaril-zstd-huffman-four-") as directory:
        work = Path(directory)
        frames = oracle["build_reference"](work)
        library = work / "zstd/lib"
        native = work / "native-huffman"
        run("cc", "-std=c11", "-Wall", "-Wextra", "-Werror", "-O2", "-I", library,
            HERE / "reference.c", library / "libzstd.a", "-o", native)
        print(f'libzstd v1.5.7 {oracle["PIN"]}')

        for alphabet, size, size_format in ((5, 2048, 1), (8, 8192, 2), (10, 24000, 3)):
            plain = samples(alphabet, size)
            frame = run(frames, "compress", data=plain)
            require(run(frames, "decode", data=frame) == plain, "native full-frame round trip")
            body, stream_bytes, count = payload(frames, frame, size_format)
            lengths, counts = check_split(work, stream_bytes, count)
            native_out = run(native, str(count), data=body)
            require(lean(work, body, "decode", len(stream_bytes), count, len(stream_bytes), count) == native_out,
                    "exact regenerated literal bytes differ")
            print(f"size format {size_format}: bytes={lengths} counts={counts} "
                  f"frame={sha256(frame).hexdigest()} literals={sha256(native_out).hexdigest()}")

        tree = bytes.fromhex("80 10")
        jump = bytes.fromhex("01 00 01 00 01 00")
        streams = bytes.fromhex("05 06 07 01")
        valid = jump + streams
        check_split(work, valid, 6)
        expected = bytes([0, 1, 1, 0, 1, 1])
        require(run(native, "6", data=tree + valid) == expected, "native zero-symbol fourth stream")
        require(lean(work, tree + valid, "decode", 10, 6) == expected, "Lean zero-symbol fourth stream")
        print("Six symbols: both accepted a marker-only fourth stream")

        for name, wire, reason in (
            ("short jump", jump[:5], "shortJumpTable"),
            ("zero first extent", b"\x00" + valid[1:], "emptyStream"),
            ("first extent past end", bytes.fromhex("01 01") + valid[2:], "invalidStreamExtent"),
            ("absent fourth stream", valid[:-1], "invalidStreamExtent"),
            ("zero fourth marker", valid[:-1] + b"\x00", "badEndMarker"),
            ("fourth stream has extra bits", valid[:-1] + b"\x03", "trailingBits"),
            ("first stream underflow", jump + b"\x01" + streams[1:], "incompleteCode"),
        ):
            result = lean(work, tree + wire, "decode", len(wire), 6)
            require(isinstance(result, str) and reason in result, f"{name}: {result!r}")
            reference = subprocess.run([native, "6"], input=tree + wire, stdout=subprocess.PIPE)
            require(reference.returncode == 3, f"{name}: expected native rejection")
            print(f"{name}: both rejected")

        for length, count, byte_cap, symbol_cap, reason in (
            (9, 6, 10, 6, "sizeMismatch"),
            (11, 6, 11, 6, "sizeMismatch"),
            (10, 5, 10, 6, "invalidRegeneratedSize"),
            (10, 6, 9, 6, "inputLimit"),
            (10, 6, 10, 5, "outputLimit"),
        ):
            failure = lean(work, valid, "split", length, count, byte_cap, symbol_cap)
            require(isinstance(failure, str) and reason in failure, f"expected {reason}: {failure!r}")
        print("Lean rejected both extent mismatches, the below-minimum count and both caller caps")


if __name__ == "__main__":
    main()
