#!/usr/bin/env python3
"""Compare canonical slots and exact one-stream output with pinned libzstd."""
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


def lean(work, data, mode, input_cap=131072, output_cap=131072):
    source, destination = work / "source", work / "decoded"
    source.write_bytes(data)
    destination.unlink(missing_ok=True)
    result = subprocess.run(
        ["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
         HERE / "Interop.lean", source, destination, str(mode), str(input_cap), str(output_cap)],
        cwd=ROOT, stdout=subprocess.PIPE, text=True,
    )
    if result.returncode == 3:
        require(not destination.exists(), "failed decode returned bytes")
        return result.stdout.strip()
    result.check_returncode()
    return destination.read_bytes()


def payload(frames, data):
    body = run(frames, "first-block", data=data)
    require((body[0] & 15) == 2, "expected a fresh one-stream Huffman literal section")
    header = int.from_bytes(body[:3], "little")
    regenerated, compressed = (header >> 4) & 1023, header >> 14
    require(3 + compressed < len(body), "literal section must leave sequence bytes")
    raw = body[3:3 + compressed]
    require(raw[0] >= 128, "expected a direct weight description")
    return raw, regenerated


def main():
    with TemporaryDirectory(prefix="silmaril-zstd-huffman-stream-") as directory:
        work = Path(directory)
        frames = oracle["build_reference"](work)
        library = work / "zstd/lib"
        native = work / "native-huffman"
        run("cc", "-std=c11", "-Wall", "-Wextra", "-Werror", "-O2", "-I", library,
            HERE / "reference.c", library / "libzstd.a", "-o", native)
        print(f'libzstd v1.5.7 {oracle["PIN"]}')

        for alphabet in (3, 4):
            source = samples(alphabet, 2048)
            frame = run(frames, "compress", data=source)
            require(run(frames, "decode", data=frame) == source, "native full-frame round trip")
            wire, count = payload(frames, frame)
            tree_bytes = 1 + (wire[0] - 127 + 1) // 2
            rows = run(native, "table", data=wire)
            require(lean(work, wire, "table") == rows, "actual canonical slot layout")
            decoded = run(native, str(count), data=wire)
            require(lean(work, wire, count, len(wire) - tree_bytes, count) == decoded, "actual literal output")
            print(f"{alphabet}-symbol source: {len(rows) // 2} native slots and {count} literal bytes agreed, "
                  f"frame={sha256(frame).hexdigest()} literals={sha256(decoded).hexdigest()}")

        descriptor = direct["direct"]([4, 3, 2, 0, 1], padding=15)
        stream = bytes.fromhex("01 0d")
        rfc = descriptor + stream
        expected = bytes((0, 1, 4, 5))
        require(lean(work, rfc, "table") == run(native, "table", data=rfc), "RFC canonical table")
        require(lean(work, rfc, 4, 2, 4) == run(native, "4", data=rfc) == expected, "RFC literal sequence")
        printed = descriptor + bytes.fromhex("10 0d")
        require(lean(work, printed, 4) == run(native, "4", data=printed) == bytes((0, 1, 5, 4)),
                "RFC printed example transposes the two equal-weight symbols")
        print("RFC erratum 8195: 01 0d decoded to 0, 1, 4, 5, and printed 10 0d to 0, 1, 5, 4")

        for name, weights in (("depth eleven", list(range(11, 0, -1))),
                              ("128 transmitted symbols", [0] * 127 + [1])):
            wire = direct["direct"](weights)
            rows = run(native, "table", data=wire)
            require(lean(work, wire, "table") == rows, f"{name}: native canonical slots")
            print(f"{name}: all {len(rows) // 2} table slots agreed")

        for name, data, count, reason in (
            ("zero marker", descriptor + b"\0", 4, "badEndMarker"),
            ("truncated payload", descriptor + stream[1:], 4, "incompleteCode"),
            ("too few expected symbols", rfc, 3, "trailingBits"),
            ("too many expected symbols", rfc, 5, "incompleteCode"),
        ):
            failure = lean(work, data, count)
            require(isinstance(failure, str) and reason in failure, f"{name}: {failure!r}")
            reference = subprocess.run([native, str(count)], input=data, stdout=subprocess.PIPE)
            require(reference.returncode == 3, f"{name}: expected native rejection")
            print(f"{name}: both rejected")

        for input_cap, output_cap, reason in ((1, 4, "inputLimit"), (2, 3, "outputLimit")):
            failure = lean(work, rfc, 4, input_cap, output_cap)
            require(isinstance(failure, str) and reason in failure, f"expected {reason}")
        print("Lean enforced exact stream byte and regenerated symbol caps")


if __name__ == "__main__":
    main()
