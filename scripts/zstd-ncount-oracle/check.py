#!/usr/bin/env python3
"""Check transmitted count prefixes and their tables with pinned libzstd."""
from hashlib import sha256
from pathlib import Path
from runpy import run_path
import subprocess
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
oracle = run_path(str(ROOT / "scripts/zstd-literal-oracle/check.py"))
run = oracle["run"]
require = oracle["require"]
PIN = oracle["PIN"]


def lean(work, data, *, byte_cap=512, symbol_cap=256, log_cap=9, expected="-"):
    source, remainder = work / "input", work / "remainder"
    source.write_bytes(data)
    remainder.unlink(missing_ok=True)
    result = subprocess.run(
        ["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
         HERE / "Interop.lean", source, remainder, str(byte_cap), str(symbol_cap), str(log_cap), str(expected)],
        cwd=ROOT, stdout=subprocess.PIPE,
    )
    if result.returncode == 3:
        return result.stdout.decode().strip()
    require(result.returncode == 0, f"Lean fixture driver failed: {result.stdout!r}")
    raw_bits, table = result.stdout.split(b"\n", 1)
    return int(raw_bits), table, remainder.read_bytes()


def expect_lean(work, data, reason, **limits):
    error = lean(work, data, **limits)
    require(isinstance(error, str) and error.endswith(reason), f"expected {reason}, got {error!r}")


def main():
    with TemporaryDirectory(prefix="silmaril-zstd-ncount-") as directory:
        work = Path(directory)
        oracle["build_reference"](work)
        library, native = work / "zstd/lib", work / "ncount-reference"
        run("cc", "-std=c11", "-O2", "-I", library, HERE / "reference.c", library / "libzstd.a", "-o", native)
        print(f"libzstd v1.5.7 {PIN}")
        specs = (
            ("even", 5, [16, 16]),
            ("byte-aligned", 5, [20, 9, 3]),
            ("skew", 5, [30, -1, -1]),
            ("short-zero-run", 5, [0, 15, -1, 0, 16]),
            ("long-zero-run", 5, [31] + [0] * 254 + [-1]),
            ("all-low", 5, [-1] * 32),
            ("largest-table", 9, [257, 0, 253, -1, -1]),
            ("middle-log", 7, [39, 16, 0, 0, 1, 0, -1, 71]),
        )
        suffix = bytes.fromhex("a5 00 ff 42 00 13 24 68 9b")
        prefixes = {}
        for name, log, counts in specs:
            header = run(native, "write", str(log), *map(str, counts))
            prefixes[name] = header
            native_table = run(native, "read", data=header + suffix)
            require(native_table.splitlines()[0] == f"{len(header)} {log} {len(counts)}".encode(),
                    f"{name}: native consumption")
            require(list(map(int, native_table.splitlines()[1].split())) == counts, f"{name}: native counts")
            bits, table, rest = lean(work, header + suffix, byte_cap=len(header), expected=len(counts))
            require((bits + 7) // 8 == len(header) and table == native_table and rest == suffix,
                    f"{name}: Lean boundary, remainder, distribution, or table")
            if name == "byte-aligned":
                require(bits == 16, "byte-aligned fixture uses every consumed bit")
            print(f"{name}: {bits} bits, {len(header)} bytes, {1 << log} states agreed, "
                  f"prefix={sha256(header).hexdigest()} table={sha256(table).hexdigest()}")

        even = prefixes["even"]
        padded = even[:-1] + bytes((even[-1] | 0xC0,))
        require(run(native, "read", data=padded + suffix) == run(native, "read", data=even + suffix),
                "native ignores padding bits")
        require(lean(work, padded + suffix) == lean(work, even + suffix), "Lean ignores padding bits")
        print(f"nonzero unused padding: both preserved the remainder, prefix={sha256(padded).hexdigest()}")

        shared, native_alternatives = 0, 0
        for name in ("even", "long-zero-run"):
            header = prefixes[name]
            for size in range(len(header)):
                partial = header[:size]
                reference = subprocess.run([native, "read"], input=partial, stdout=subprocess.PIPE)
                expect_lean(work, partial, "truncated")
                if name == "long-zero-run" and size >= 8:
                    require(reference.returncode == 0, f"{name}/{size}: expected pinned native alternative")
                    consumed, _, symbols = map(int, reference.stdout.splitlines()[0].split())
                    require(consumed <= size and symbols < 256, "native alternative differs from full prefix")
                    print(f"{name}/{size}: libzstd consumed {consumed} bytes for {symbols} symbols, Lean truncated")
                    native_alternatives += 1
                else:
                    require(reference.returncode == 3, f"{name}/{size}: expected native truncation")
                    shared += 1
        print(f"{shared} shorter prefixes rejected by both, {native_alternatives} rejected only by Lean")

        expect_lean(work, even + suffix, "byteLimit", byte_cap=len(even) - 1)
        expect_lean(work, even + suffix, "wrongSymbolCount", expected=3)
        expect_lean(work, prefixes["long-zero-run"] + suffix, "symbolLimit", symbol_cap=255)
        expect_lean(work, prefixes["largest-table"] + suffix, "accuracyLog", log_cap=8)
        expect_lean(work, bytes.fromhex("f0 03") + suffix, "tooFewSymbols")
        print("prefix, symbol, and accuracy caps, expected count, and singleton distribution: Lean rejected")


if __name__ == "__main__":
    main()
