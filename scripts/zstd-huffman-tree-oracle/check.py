#!/usr/bin/env python3
"""Compare both Huffman tree descriptions and canonical X1 slots with libzstd."""
from hashlib import sha256
from pathlib import Path
from runpy import run_path
import subprocess
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
source_fixtures = run_path(str(ROOT / "scripts/zstd-huffman-weights-oracle/check.py"))
run, require, sample = (source_fixtures[name] for name in ("run", "require", "sample"))
direct, oracle = source_fixtures["direct"], source_fixtures["oracle"]


def lean(work, wire, *, cap=128, symbols=256, depth=11):
    source, table, suffix = (work / name for name in ("payload", "slots", "literals"))
    source.write_bytes(wire)
    table.unlink(missing_ok=True)
    suffix.unlink(missing_ok=True)
    result = subprocess.run(
        ["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
         HERE / "Interop.lean", source, table, suffix, str(cap), str(symbols), str(depth)],
        cwd=ROOT, stdout=subprocess.PIPE,
    )
    if result.returncode == 3:
        require(not table.exists() and not suffix.exists(), "failure returned a partial result")
        return result.stdout.decode().strip()
    result.check_returncode()
    return result.stdout, table.read_bytes(), suffix.read_bytes()


def expect_error(work, wire, stage, reason, **limits):
    observed = lean(work, wire, **limits)
    require(isinstance(observed, str) and f"Error.{stage}" in observed
            and observed.rstrip(")").endswith("." + reason),
            f"expected {stage}/{reason}, got {observed!r}")


def main():
    with TemporaryDirectory(prefix="silmaril-zstd-huffman-tree-") as directory:
        work = Path(directory)
        frames = oracle["build_reference"](work)
        library = work / "zstd/lib"
        stats, table, explicit = (work / name for name in ("stats", "table", "explicit"))
        for executable, topic in ((stats, "direct"), (table, "stream"), (explicit, "fse-weights")):
            source = ROOT / f"scripts/zstd-huffman-{topic}-oracle/reference.c"
            run("cc", "-std=c11", "-Wall", "-Wextra", "-Werror", "-O2", "-I", library,
                source, library / "libzstd.a", "-o", executable)
        print(f'libzstd v1.5.7 {oracle["PIN"]}')

        def compare(mode, payload, expected_symbols):
            metadata, weights = run(stats, data=payload).splitlines()
            size, depth, symbols = map(int, metadata.split())
            require(symbols == expected_symbols, "unexpected completed symbol count")
            native_rows = run(table, "table", data=payload)
            require(len(native_rows) == 2 * (1 << depth), "unexpected native slot count")
            expected = mode.encode() + b" " + metadata + b"\n" + weights + b"\n"
            require(lean(work, payload, cap=size, symbols=symbols, depth=depth) ==
                    (expected, native_rows, payload[size:]), "completed tree, slots or extent differ")
            expect_error(work, payload, mode, "byteLimit", cap=size - 1)
            expect_error(work, payload, mode, "symbolLimit" if mode == "direct" else "weightLimit",
                         symbols=symbols - 1)
            expect_error(work, payload, "direct" if mode == "direct" else "completion",
                         "depthLimit", depth=depth - 1)
            print(f"{mode}/{symbols}: {size} bytes, depth {depth}, {1 << depth} slots, "
                  f"description={sha256(payload[:size]).hexdigest()} slots={sha256(native_rows).hexdigest()}")

        for mode, plain, symbols in (
            ("direct", direct["samples"](3, 2048), 3),
            ("fse", sample(160), 160),
            ("fse", sample(256), 256),
        ):
            frame = run(frames, "compress", data=plain)
            require(run(frames, "decode", data=frame) == plain, "native frame decode")
            payload, _ = direct["huffman_payload"](frames, frame)
            require((payload[0] >= 128) == (mode == "direct"), "descriptor mode changed")
            compare(mode, payload, symbols)

        suffix = bytes.fromhex("00 ff 42")
        compare("direct", direct["direct"]([0] * 127 + [1]) + suffix, 129)
        for wire_hex, weights, reason in (
            ("04 10 3f 02 04", [0, 0], "zeroMass"),
            ("06 10 88 c1 07 60 04", [3, 1], "nonPowerRemainder"),
            ("05 01 45 3f cc 12", [2, 2], "invalidDeepestRank"),
        ):
            payload = bytes.fromhex(wire_hex) + suffix
            require(run(explicit, data=payload) == bytes(weights), "valid native FSE emission")
            require(subprocess.run([stats], input=payload, stdout=subprocess.PIPE).returncode == 3,
                    "native Huffman reader accepted an invalid completed tree")
            expect_error(work, payload, "completion", reason)
            print(f"FSE emitted {weights}; tree completion rejected {reason}, wire={wire_hex}")


if __name__ == "__main__":
    main()
