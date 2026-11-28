#!/usr/bin/env python3
"""Compare sequence prefixes with pinned libzstd v1.5.7."""
from hashlib import sha256
from pathlib import Path
from runpy import run_path
import subprocess
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
oracle = run_path(str(ROOT / "scripts/zstd-literal-oracle/check.py"))
run, require, frame = (oracle[name] for name in ("run", "require", "frame"))
PIN = oracle["PIN"]

MAX_BLOCK = 131072
MAX_SEQUENCES = 98047


def lean(work, data, byte_cap=MAX_BLOCK, seq_cap=MAX_SEQUENCES):
    path, tail = work / "input", work / "tail"
    path.write_bytes(data)
    result = subprocess.run(
        ["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
         HERE / "Interop.lean", path, tail, str(byte_cap), str(seq_cap)],
        cwd=ROOT, stdout=subprocess.PIPE,
    )
    if result.returncode == 3:
        return result.stdout.decode().strip()
    result.check_returncode()
    return result.stdout, tail.read_bytes()


def tables_from(native_output):
    lines = iter(native_output.splitlines())
    consumed, count = map(int, next(lines).split())
    tables = []
    for _ in range(3 if count else 0):
        log = int(next(lines))
        rows = [tuple(map(int, next(lines).split())) for _ in range(1 << log)]
        tables.append((log, rows))
    require(next(lines, None) is None, "unexpected native output")
    return consumed, count, tables


def bitstream(fields):
    # Appending fields in decoder order places the marker above the first field.
    bits, size = 1, 1
    for value, width in fields:
        require(0 <= value < 1 << width, "invalid fixture bit field")
        bits = (bits << width) | value
        size += width
    return bits.to_bytes((size + 7) // 8, "little")


def main():
    with TemporaryDirectory(prefix="silmaril-zstd-sequence-tables-") as directory:
        work = Path(directory)
        frames = oracle["build_reference"](work)
        library = work / "zstd/lib"
        native, counts = work / "seq-header", work / "ncount"
        run("cc", "-std=c11", "-O2", "-Wall", "-Wextra", "-Werror", "-I", library,
            HERE / "reference.c", library / "libzstd.a", "-o", native)
        run("cc", "-std=c11", "-O2", "-I", library, ROOT / "scripts/zstd-ncount-oracle/reference.c",
            library / "libzstd.a", "-o", counts)
        print(f"libzstd v1.5.7 {PIN}")

        symbols = (4, 2, 0)
        distributions = ([0, 0, 0, 0, 31, -1], [0, 0, 16, 16], [16, 16])
        descriptions = [
            (b"", bytes([symbol]), run(counts, "write", "5", *map(str, weights)))
            for symbol, weights in zip(symbols, distributions)
        ]

        for modes in ((0, 1, 2), (2, 0, 1), (1, 2, 0), (2, 2, 2), (0, 0, 0), (1, 1, 1)):
            ll_mode, of_mode, ml_mode = modes
            prefix = bytes([1, ll_mode * 64 + of_mode * 16 + ml_mode * 4])
            prefix += b"".join(options[mode] for options, mode in zip(descriptions, modes))

            # Use libzstd's independently built states to encode one command:
            # four literals, then a three-byte match at distance four.
            _, _, tables = tables_from(run(native, data=prefix + b"\x01"))
            codes = ((4, 0), (1, 2), (3, 0))  # native base and additional width
            fields = [
                (next(i for i, row in enumerate(rows) if row[2:] == code), log)
                for (log, rows), code in zip(tables, codes)
            ]
            stream = bitstream(fields + [(3, 2)])
            section = prefix + stream
            expected = run(native, data=section)
            consumed, count, tables = tables_from(expected)
            require((consumed, count) == (len(prefix), 1), f"{modes}: native prefix")
            require(lean(work, section, len(section), 1) == (expected, stream),
                    f"{modes}: Lean extent, rows, or remainder")
            full = frame(b"\x20abcd" + section)
            require(run(frames, "decode", data=full) == b"abcdabc", f"{modes}: native frame output")
            print(f"{modes}: {consumed} prefix bytes, {sum(len(rows) for _, rows in tables)} rows, "
                  f"frame={sha256(full).hexdigest()}")

        largest = ((9, [0, 0, 0, 0, 511, -1]), (8, [0, 0, 128, 128]), (9, [256, 256]))
        prefix = bytes.fromhex("01 a8") + b"".join(
            run(counts, "write", str(log), *map(str, weights)) for log, weights in largest
        )
        stream = bytes.fromhex("00 42 a5")
        expected = run(native, data=prefix + stream)
        consumed, count, tables = tables_from(expected)
        require((consumed, count) == (len(prefix), 1), "maximum log prefix")
        require([log for log, _ in tables] == [9, 8, 9], "maximum logs")
        require(lean(work, prefix + stream) == (expected, stream), "maximum log rows or remainder")
        print("Maximum alphabet accuracy logs 9, 8, 9: all 1280 rows agreed")

        for encoded, count in (("00", 0), ("80 00", 0), ("80 80 00 01", 128),
                               ("ff 00 00 00 01", 32512), ("ff ff ff 00 01", MAX_SEQUENCES)):
            section = bytes.fromhex(encoded)
            expected = run(native, data=section)
            consumed, got, _ = tables_from(expected)
            require(got == count, f"{encoded}: native count")
            require(lean(work, section, len(section), count) == (expected, section[consumed:]),
                    f"{encoded}: Lean count or suffix")
        print("Both resolved zero, two-byte zero, and two- and three-byte positive counts")

        rejected = (
            ("empty input", "", "truncated"),
            ("truncated long count", "ff 00", "truncated"),
            ("zero count with trailing input", "00 00", "trailingEmptySection"),
            ("missing mode byte", "01", "missingModes"),
            ("reserved mode bits", "01 01 01", "reservedBits"),
            ("missing RLE symbol", "01 40", "missingRleSymbol"),
            ("literal code out of range", "01 40 24 01", "invalidRleSymbol"),
            ("offset code out of range", "01 10 20 01", "invalidRleSymbol"),
            ("match code out of range", "01 04 35 01", "invalidRleSymbol"),
            ("truncated normalized counts", "01 80 f0", "truncated"),
            ("offset accuracy log nine", "01 20 04 01", "accuracyLog"),
            ("repeat without prior tables", "01 0c 01", "unsupportedMode"),
        )
        for name, encoded, reason in rejected:
            section = bytes.fromhex(encoded)
            observed = subprocess.run([native], input=section, stdout=subprocess.PIPE)
            require(observed.returncode == 3, f"{name}: expected native rejection")
            failure = lean(work, section)
            require(isinstance(failure, str) and reason in failure, f"{name}: {failure!r}")
            print(f"{name}: both rejected")

        for encoded, reason, byte_cap, seq_cap in (
            ("01 00", "missingBitstream", 2, 1),
            ("01 00 01", "inputLimit", 2, 1),
            ("01 00 01", "sequenceLimit", 3, 0),
        ):
            failure = lean(work, bytes.fromhex(encoded), byte_cap, seq_cap)
            require(isinstance(failure, str) and reason in failure, f"expected {reason}, got {failure!r}")
        missing = subprocess.run([frames, "decode"], input=frame(bytes.fromhex("00 01 00")),
                                 stdout=subprocess.PIPE)
        require(missing.returncode == 3, "native full-frame decoder must reject a missing bitstream")
        print("Absent reverse stream rejected by Lean and full native decode; Lean enforced both caller caps")


if __name__ == "__main__":
    main()
