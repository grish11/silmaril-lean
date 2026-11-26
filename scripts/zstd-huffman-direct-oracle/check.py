#!/usr/bin/env python3
"""Compare direct tree descriptions with pinned libzstd HUF_readStats."""
from hashlib import sha256
from pathlib import Path
from runpy import run_path
import subprocess
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
oracle = run_path(str(ROOT / "scripts/zstd-literal-oracle/check.py"))
run, require = oracle["run"], oracle["require"]


def lean(work, data, *, bytes_cap=65, symbols=129, depth=11):
    source, destination = work / "description", work / "suffix"
    source.write_bytes(data)
    destination.unlink(missing_ok=True)
    result = subprocess.run(
        ["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
         HERE / "Interop.lean", source, destination, str(bytes_cap), str(symbols), str(depth)],
        cwd=ROOT, stdout=subprocess.PIPE,
    )
    if result.returncode == 3:
        require(not destination.exists(), "rejected prefix returned a suffix")
        return result.stdout.decode().strip()
    result.check_returncode()
    return result.stdout, destination.read_bytes()


def direct(weights, padding=0):
    count = len(weights)
    require(1 <= count <= 128, "invalid fixture symbol count")
    nibbles = weights + ([padding] if count % 2 else [])
    return bytes([count + 127] + [16 * high + low for high, low in zip(nibbles[::2], nibbles[1::2])])


def huffman_payload(native, frame):
    body = run(native, "first-block", data=frame)
    require((body[0] & 3) == 2, "expected a Huffman literal section with a fresh tree")
    size_format = (body[0] >> 2) & 3
    header_size, width = ((3, 10), (3, 10), (4, 14), (5, 18))[size_format]
    packed = int.from_bytes(body[:header_size], "little")
    compressed_size = packed >> (4 + width)
    require(header_size + compressed_size < len(body), "literal section must leave sequence bytes")
    return body[header_size:header_size + compressed_size], 1 if size_format == 0 else 4


def samples(alphabet, size, bias=0):
    source = (sha256(counter.to_bytes(4, "little")).digest() for counter in range((size + 31) // 32))
    return bytes(bias + byte % alphabet for chunk in source for byte in chunk)[:size]


def compare(native, work, body, size=None, expected=None):
    result = run(native, data=body)
    used, depth, count = map(int, result.splitlines()[0].split())
    require(size is None or used == size, "native prefix boundary")
    if expected is not None:
        require(list(map(int, result.splitlines()[1].split())) == expected, "inferred weights")
    require(lean(work, body, bytes_cap=used, symbols=count, depth=depth) == (result, body[used:]),
            "Lean weights, depth, consumed bytes or untouched suffix differ")
    return used, depth, count


def main():
    with TemporaryDirectory(prefix="silmaril-zstd-huffman-direct-") as directory:
        work = Path(directory)
        frames = oracle["build_reference"](work)
        library = work / "zstd/lib"
        native = work / "read-stats"
        run("cc", "-std=c11", "-Wall", "-Wextra", "-Werror", "-O2", "-I", library,
            HERE / "reference.c", library / "libzstd.a", "-o", native)
        print(f'libzstd v1.5.7 {oracle["PIN"]}')

        for alphabet, size in ((3, 2048), (4, 2048), (8, 8192)):
            plain = samples(alphabet, size)
            frame = run(frames, "compress", data=plain)
            require(run(frames, "decode", data=frame) == plain, "native frame decode")
            body, streams = huffman_payload(frames, frame)
            require(body[0] >= 128, "expected a real direct tree descriptor")
            count = body[0] - 127
            used, depth, symbols = compare(native, work, body, 1 + (count + 1) // 2)
            require(len(body[used:]) > 0, "actual Huffman streams remain after the descriptor")
            print(f"{streams}-stream native frame: {used} prefix bytes, {symbols} symbols, depth {depth}, "
                  f"prefix={body[:used].hex()} frame={sha256(frame).hexdigest()}")

        tail = bytes.fromhex("05 00 ff 01 5a")
        for name, weights, last, padding in (
            ("RFC example", [4, 3, 2, 0, 1], 1, 15),
            ("inferred weight two", [3, 1, 1], 2, 0),
            ("maximum transmitted symbols", [0] * 127 + [1], 1, 0),
            ("RFC maximum depth eleven", list(range(11, 0, -1)), 1, 9),
        ):
            wire = direct(weights, padding)
            used, depth, count = compare(native, work, wire + tail, len(wire), weights + [last])
            print(f"{name}: {used} prefix bytes, {count} symbols, depth {depth}")

        def both_reject(name, wire, reason):
            reference = subprocess.run([native], input=wire, stdout=subprocess.PIPE)
            require(reference.returncode == 3, f"{name}: native should reject")
            result = lean(work, wire)
            require(isinstance(result, str) and reason in result, f"{name}: got {result!r}")

        rfc = direct([4, 3, 2, 0, 1])
        for size in range(len(rfc)):
            both_reject(f"truncated/{size}", rfc[:size], "truncated")
        both_reject("zero mass", direct([0]), "zeroMass")
        both_reject("non-power remainder", direct([3, 1]), "nonPowerRemainder")
        both_reject("invalid deepest rank", direct([2]), "invalidDeepestRank")
        print("Both rejected all four RFC example truncations, zero mass, non-power remainder and invalid rank")

        too_deep = direct(list(range(12, 0, -1)))
        native_depth = int(run(native, data=too_deep).split()[1])
        require(native_depth == 12, "pinned native depth extension")
        require(lean(work, too_deep, depth=12).endswith("depthLimit"), "RFC depth ceiling must be eleven")
        print("Depth 12: native HUF_readStats accepted, Lean rejected by the RFC ceiling")

        source = samples(16, 8192, 145)
        compressed = run(frames, "compress", data=source)
        body, _ = huffman_payload(frames, compressed)
        require(body[0] < 128, "expected an actual FSE weight descriptor")
        require(run(frames, "decode", data=compressed) == source, "native FSE-weight frame")
        require(int(run(native, data=body).split()[0]) == body[0] + 1, "native FSE tree extent")
        require("unsupportedFse" in lean(work, body), "FSE weight description must fail closed")
        print(f"Native FSE weights explicitly classified as unsupported, frame={sha256(compressed).hexdigest()}")

        for limits, reason in (({"bytes_cap": 3}, "byteLimit"), ({"symbols": 5}, "symbolLimit"),
                               ({"depth": 3}, "depthLimit")):
            require(lean(work, rfc + tail, **limits).endswith(reason), f"expected {reason}")
        print("Lean enforced caller byte, symbol and depth caps")


if __name__ == "__main__":
    main()
