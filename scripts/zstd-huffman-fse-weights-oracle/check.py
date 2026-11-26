#!/usr/bin/env python3
"""Compare the complete explicit FSE weight list with pinned libzstd."""
from hashlib import sha256
from pathlib import Path
from runpy import run_path
import subprocess
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
DIRECT = ROOT / "scripts/zstd-huffman-direct-oracle"
source_fixtures = run_path(str(ROOT / "scripts/zstd-huffman-weights-oracle/check.py"))
run, require, sample = (source_fixtures[name] for name in ("run", "require", "sample"))
direct, oracle = source_fixtures["direct"], source_fixtures["oracle"]


def lean(work, wire, count=255, byte_cap=128):
    source, output, suffix = (work / name for name in ("payload", "weights", "literals"))
    source.write_bytes(wire)
    output.unlink(missing_ok=True)
    suffix.unlink(missing_ok=True)
    result = subprocess.run(
        ["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
         HERE / "Interop.lean", source, output, suffix, str(byte_cap), str(count)],
        cwd=ROOT, stdout=subprocess.PIPE,
    )
    if result.returncode == 3:
        require(not output.exists() and not suffix.exists(), "failure returned a partial result")
        return result.stdout.decode().strip()
    result.check_returncode()
    return int(result.stdout), output.read_bytes(), suffix.read_bytes()


def description(count_prefix, log, state1, state2, remaining):
    bits = f"{state1:0{log}b}{state2:0{log}b}" + remaining
    stream = int("1" + bits, 2).to_bytes((len(bits) + 8) // 8, "little")
    body = count_prefix + stream
    return bytes([len(body)]) + body


def main():
    with TemporaryDirectory(prefix="silmaril-zstd-huffman-fse-weights-") as directory:
        work = Path(directory)
        frames = oracle["build_reference"](work)
        library = work / "zstd/lib"
        native = work / "read-explicit"
        stats = work / "read-stats"
        for executable, source in ((native, HERE / "reference.c"), (stats, DIRECT / "reference.c")):
            run("cc", "-std=c11", "-Wall", "-Wextra", "-Werror", "-O2", "-I", library,
                source, library / "libzstd.a", "-o", executable)
        print(f'libzstd v1.5.7 {oracle["PIN"]}')

        for symbols in (160, 256):
            plain = sample(symbols)
            frame = run(frames, "compress", data=plain)
            require(run(frames, "decode", data=frame) == plain, "native frame decode")
            payload, streams = direct["huffman_payload"](frames, frame)
            require(streams == 4 and 0 < payload[0] < 128, "expected fresh FSE weights")
            extent = 1 + payload[0]
            header, ordered_weights = run(stats, data=payload).splitlines()
            native_extent, _, native_symbols = map(int, header.split())
            expected = bytes(map(int, ordered_weights.split()))[:-1]
            require(native_extent == extent and native_symbols == symbols, "native tree extent or count")
            require(len(expected) == symbols - 1 and run(native, data=payload) == expected,
                    "native raw weights must agree with HUF_readStats before inference")
            require(lean(work, payload, len(expected), extent) == (extent, expected, payload[extent:]),
                    "Lean explicit weights, consumed bytes or literal suffix differ")
            require(lean(work, payload, len(expected) - 1).endswith("weightLimit"), "caller weight cap")
            require(lean(work, payload, byte_cap=extent - 1).endswith("byteLimit"), "caller byte cap")
            print(f"{symbols} tree symbols: {len(expected)} explicit weights agreed, "
                  f"weights={sha256(expected).hexdigest()} prefix={sha256(payload[:extent]).hexdigest()} "
                  f"frame={sha256(frame).hexdigest()}")

        # Pinned FSE_writeNCount for [16, 16] at log 5 and [15, 16, 33] at log 6.
        even, skew = bytes.fromhex("10 3f"), bytes.fromhex("01 45 3f")
        tail = bytes.fromhex("00 ff 42")
        cases = (
            ("overflow on State1", description(even, 5, 0, 3, ""), [0, 1]),
            ("exact field then overflow on State2", description(even, 5, 0, 3, "1"), [0, 1, 0]),
            ("nonempty short field", description(skew, 6, 0, 5, "11"), [0, 1]),
            ("zero-bit update before overflow", description(skew, 6, 62, 5, ""), [2, 1, 0]),
        )
        for name, wire, output in cases:
            expected = bytes(output)
            require(run(native, data=wire + tail) == expected, f"{name}: native explicit weights")
            require(lean(work, wire + tail, len(output)) == (len(wire), expected, tail),
                    f"{name}: Lean explicit weights or suffix")
            require(lean(work, wire, len(output) - 1).endswith("weightLimit"), f"{name}: short cap")
            print(f"{name}: {output} agreed, wire={wire.hex()}")

        too_many = description(even, 5, 0, 3, "0" * 254)
        require(len(run(native, data=too_many)) == 256, "synthetic raw FSE count")
        require(lean(work, too_many, 256).endswith("weightLimit"), "RFC maximum 255 explicit weights")
        require(subprocess.run([stats], input=too_many, stdout=subprocess.PIPE).returncode == 3,
                "native Huffman description must reject the oversized output")
        print("The RFC cap rejected 256 weights that the generic libzstd FSE decoder emitted")

        for wire, reason in (
            (cases[0][1][:-1], "truncated"),
            (bytes.fromhex("03 10 3f 00"), "badEndMarker"),
            (bytes.fromhex("03 10 3f 01"), "truncatedStates"),
            (bytes.fromhex("03 10 3f 20"), "truncatedStates"),
        ):
            require(subprocess.run([native], input=wire, stdout=subprocess.PIPE).returncode == 3,
                    f"native accepted malformed description {wire.hex()}")
            observed = lean(work, wire)
            require(isinstance(observed, str) and reason in observed, f"expected {reason}, got {observed!r}")
        print("Both rejected malformed extent, marker and incomplete initialization fields")


if __name__ == "__main__":
    main()
