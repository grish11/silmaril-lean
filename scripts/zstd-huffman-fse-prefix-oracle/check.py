#!/usr/bin/env python3
"""Check FSE weight descriptions through the ordered initial-state fields."""
from hashlib import sha256
from pathlib import Path
from runpy import run_path
import subprocess
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
WEIGHTS = ROOT / "scripts/zstd-huffman-weights-oracle"
weights = run_path(str(WEIGHTS / "check.py"))
run, require, sample = (weights[name] for name in ("run", "require", "sample"))
direct, oracle = weights["direct"], weights["oracle"]


def lean(work, wire, cap=128):
    source, destination = work / "literal-payload", work / "literal-streams"
    source.write_bytes(wire)
    destination.unlink(missing_ok=True)
    result = subprocess.run(
        ["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
         HERE / "Interop.lean", source, destination, str(cap)], cwd=ROOT, stdout=subprocess.PIPE,
    )
    if result.returncode == 3:
        require(not destination.exists(), "rejected prefix returned a suffix")
        return result.stdout.decode().strip()
    result.check_returncode()
    return result.stdout, destination.read_bytes()


def description(body):
    require(0 < len(body) < 128, "invalid fixture description size")
    return bytes([len(body)]) + body


def main():
    with TemporaryDirectory(prefix="silmaril-zstd-huffman-fse-prefix-") as directory:
        work = Path(directory)
        frames = oracle["build_reference"](work)
        library = work / "zstd/lib"
        native = work / "fse-prefix"
        run("cc", "-std=c11", "-Wall", "-Wextra", "-Werror", "-O2", "-I", library,
            HERE / "reference.c", library / "libzstd.a", "-o", native)
        print(f'libzstd v1.5.7 {oracle["PIN"]}')

        fixtures = []
        for symbols in (160, 256):
            plain = sample(symbols)
            frame = run(frames, "compress", data=plain)
            require(run(frames, "decode", data=frame) == plain, "native frame decode")
            payload, streams = direct["huffman_payload"](frames, frame)
            require(streams == 4 and 0 < payload[0] < 128, "expected fresh FSE weight description")
            native_result = run(native, data=payload)
            size, counts, log, first, second, remaining = map(int, native_result.splitlines()[0].split())
            require(size == 1 + payload[0] and counts < size - 1, "native wire boundaries")
            require(lean(work, payload, size) == (native_result, payload[size:]),
                    "normalized counts, rows, initial states, reverse bits or literal suffix differ")
            require(lean(work, payload, size - 1).endswith("byteLimit"), "caller byte cap")
            fixtures.append((payload[:size], counts, log))
            print(f"{symbols} symbols: extent={size} NCount={counts} log={log}, "
                  f"states=({first}, {second}), remaining={remaining}, rows={1 << log}, "
                  f"prefix={sha256(payload[:size]).hexdigest()} frame={sha256(frame).hexdigest()}")

        def both_reject(wire, reason):
            native_result = subprocess.run([native], input=wire, stdout=subprocess.PIPE)
            require(native_result.returncode == 3, f"native accepted {reason}")
            observed = lean(work, wire)
            require(isinstance(observed, str) and reason in observed, f"expected {reason}, got {observed!r}")

        # FSE_writeNCount(log=6, counts=[15,16,33]) produced 01 45 3f.
        at_limit = bytes.fromhex("05 01 45 3f 93 13")
        native_result = run(native, data=at_limit)
        require(native_result.splitlines()[0] == b"6 3 6 14 19 0", "log-6 boundary metadata")
        require(lean(work, at_limit) == (native_result, b""), "log-6 boundary or empty bit suffix")
        print("Log 6: all 64 rows and both states agreed with exactly zero unread bits")

        wire, count_bytes, log = fixtures[0]
        count_prefix = wire[1:1 + count_bytes]
        both_reject(b"", "truncated")
        both_reject(b"\x00", "emptyDescription")
        both_reject(direct["direct"]([1]), "directMode")
        both_reject(wire[:-1], "truncated")
        both_reject(description(b"\x00"), "counts")
        both_reject(description(bytes([(wire[1] & 0xF0) | 2]) + wire[2:]), "accuracyLog")
        both_reject(description(count_prefix), "badEndMarker")
        both_reject(description(count_prefix) + wire[1 + count_bytes:], "badEndMarker")
        both_reject(description(count_prefix + b"\x00"), "badEndMarker")
        both_reject(description(count_prefix + b"\x01"), "truncatedStates")
        both_reject(description(count_prefix + bytes([1 << log])), "truncatedStates")
        # FSE_writeNCount(log=5, counts=[16] + [0]*11 + [16]) gave 10 e3 ef 03.
        both_reject(bytes.fromhex("06 10 e3 ef 03 93 13"), "symbolLimit")
        print("Both rejected twelve controls covering mode, extent, counts, marker and state initialization")
        print("Lean enforced the exact caller byte cap")


if __name__ == "__main__":
    main()
