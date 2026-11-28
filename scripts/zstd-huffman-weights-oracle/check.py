#!/usr/bin/env python3
"""Compare completion of already decoded Huffman weights with pinned libzstd."""
from hashlib import sha256
from pathlib import Path
from runpy import run_path
import subprocess
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
DIRECT = ROOT / "scripts/zstd-huffman-direct-oracle"
direct = run_path(str(DIRECT / "check.py"))
run, require = direct["run"], direct["require"]
oracle = direct["oracle"]


def lean(work, weights, symbols=256, depth=11):
    source = work / "transmitted"
    source.write_bytes(bytes(weights))
    result = subprocess.run(
        ["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
         HERE / "Interop.lean", source, str(symbols), str(depth)],
        cwd=ROOT, stdout=subprocess.PIPE,
    )
    if result.returncode == 3:
        return result.stdout.decode().strip()
    result.check_returncode()
    return result.stdout


def sample(alphabet):
    entropy = b"".join(sha256(counter.to_bytes(4, "little")).digest() for counter in range(3000))
    return bytes(range(alphabet)) + bytes(
        value % (alphabet if selector < 64 else 16)
        for selector, value in zip(entropy[::2], entropy[1::2])
    )


def compare(native, work, payload, used, depth, count):
    header, weights = run(native, data=payload).splitlines()
    require(list(map(int, header.split())) == [used, depth, count], "native tree metadata")
    explicit = list(map(int, weights.split()))[:-1]
    expected = f"{depth} {count}\n".encode() + weights + b"\n"
    require(lean(work, explicit, symbols=count, depth=depth) == expected, "Lean tree differs")
    return explicit


def main():
    with TemporaryDirectory(prefix="silmaril-zstd-huffman-weights-") as directory:
        work = Path(directory)
        frames = oracle["build_reference"](work)
        library = work / "zstd/lib"
        native = work / "read-stats"
        run("cc", "-std=c11", "-Wall", "-Wextra", "-Werror", "-O2", "-I", library,
            DIRECT / "reference.c", library / "libzstd.a", "-o", native)
        print(f'libzstd v1.5.7 {oracle["PIN"]}')

        for count, depth in ((160, 10), (256, 11)):
            plain = sample(count)
            frame = run(frames, "compress", data=plain)
            require(run(frames, "decode", data=frame) == plain, "native frame decode")
            body, streams = direct["huffman_payload"](frames, frame)
            require(0 < body[0] < 128 and streams == 4, "actual FSE weight prefix")
            size = 1 + body[0]
            explicit = compare(native, work, body, size, depth, count)
            require(len(explicit) == count - 1, "explicit symbol count")
            for symbols, cap, reason in ((count - 1, depth, "symbolLimit"), (count, depth - 1, "depthLimit")):
                require(lean(work, explicit, symbols, cap).endswith(reason), f"expected {reason}")
            print(f"{count} symbols, depth {depth}: {size}-byte FSE prefix, "
                  f"frame={sha256(frame).hexdigest()} prefix={sha256(body[:size]).hexdigest()}")

        for explicit, reason in (([0], "zeroMass"), ([3, 1], "nonPowerRemainder"), ([2], "invalidDeepestRank")):
            result = subprocess.run([native], input=direct["direct"](explicit), stdout=subprocess.PIPE)
            require(result.returncode == 3, f"native must reject {reason}")
            require(lean(work, explicit).endswith(reason), f"Lean must reject {reason}")
        print("Both rejected zero mass, non-power remainder and invalid deepest rank")

        require(lean(work, [1] + [0] * 255, symbols=257).endswith("symbolLimit"), "256 transmitted weights")
        too_deep = list(range(12, 0, -1))
        require(int(run(native, data=direct["direct"](too_deep)).split()[1]) == 12, "native depth extension")
        require(lean(work, too_deep, depth=12).endswith("depthLimit"), "RFC depth ceiling")
        print("Lean enforced caller caps, the 255 explicit-weight ceiling and the RFC depth-11 ceiling")


if __name__ == "__main__":
    main()
