#!/usr/bin/env python3
"""Compare new-tree literal sections with the pinned libzstd literal decoder."""
from hashlib import sha256
from pathlib import Path
from runpy import run_path
import subprocess
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
fixtures = run_path(str(ROOT / "scripts/zstd-huffman-weights-oracle/check.py"))
run, require, sample = (fixtures[name] for name in ("run", "require", "sample"))
samples, oracle = fixtures["direct"]["samples"], fixtures["oracle"]
FORMATS = ((3, 10), (3, 10), (4, 14), (5, 18))


def lean(work, wire, *, input_cap=131072, output_cap=131072):
    source, output, suffix = (work / name for name in ("input", "literals", "suffix"))
    source.write_bytes(wire)
    output.unlink(missing_ok=True)
    suffix.unlink(missing_ok=True)
    result = subprocess.run(
        ["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
         HERE / "Interop.lean", source, output, suffix, str(input_cap), str(output_cap)],
        cwd=ROOT, stdout=subprocess.PIPE,
    )
    if result.returncode == 3:
        require(not output.exists() and not suffix.exists(), "failure returned partial bytes")
        return result.stdout.decode().strip()
    result.check_returncode()
    return tuple(map(int, result.stdout.split())), output.read_bytes(), suffix.read_bytes()


def expect_error(work, wire, stage, reason, **caps):
    observed = lean(work, wire, **caps)
    require(isinstance(observed, str) and f"Error.{stage}" in observed
            and observed.rstrip(")").endswith("." + reason),
            f"expected {stage}/{reason}, got {observed!r}")


def section(fmt, regenerated, payload, *, size=None, kind=2):
    header_size, width = FORMATS[fmt]
    compressed = len(payload) if size is None else size
    packed = kind + 4 * fmt + (regenerated << 4) + (compressed << (4 + width))
    return packed.to_bytes(header_size, "little") + payload


def main():
    with TemporaryDirectory(prefix="silmaril-zstd-huffman-literal-section-") as directory:
        work = Path(directory)
        frames = oracle["build_reference"](work)
        library = work / "zstd/lib"
        native = work / "native-literals"
        run("cc", "-std=c11", "-Wall", "-Wextra", "-Werror", "-O2", "-I", library,
            HERE / "reference.c", library / "libzstd.a", "-o", native)
        print(f'libzstd v1.5.7 {oracle["PIN"]}')

        def compare(wire, fmt, mode, expected=None):
            header_size, width = FORMATS[fmt]
            require(wire[0] & 15 == 2 + 4 * fmt, "unexpected literal header")
            require((wire[header_size] >= 128) == (mode == "direct"), "tree mode changed")
            packed = int.from_bytes(wire[:header_size], "little")
            claimed = packed >> (4 + width)
            metadata, literals = run(native, data=wire).split(b"\n", 1)
            used, size = map(int, metadata.split())
            require(used == header_size + claimed < len(wire), "native extent must leave a following suffix")
            require(size == len(literals) == (packed >> 4) % (1 << width), "native regenerated size")
            require(expected is None or literals == expected, "known literal bytes")
            require(lean(work, wire, input_cap=used, output_cap=size) ==
                    ((fmt, claimed, size, used), literals, wire[used:]), "Lean header, literals, or suffix differ")
            return used, size, literals

        for fmt, mode, plain in (
            (0, "direct", samples(3, 2048)),
            (0, "fse", samples(4, 1024, 145)),
            (1, "direct", samples(5, 2048)),
            (2, "direct", samples(8, 8192)),
            (3, "direct", samples(10, 24000)),
            (3, "fse", sample(256)),
        ):
            frame = run(frames, "compress", data=plain)
            require(run(frames, "decode", data=frame) == plain, "native frame decode")
            body = run(frames, "first-block", data=frame)
            used, size, literals = compare(body, fmt, mode)
            print(f"format {fmt}/{mode}: {used} section bytes, {size} literals, "
                  f"frame={sha256(frame).hexdigest()} section={sha256(body[:used]).hexdigest()} "
                  f"literals={sha256(literals).hexdigest()}")

        tree = bytes.fromhex("80 10")
        jump = bytes.fromhex("01 00 01 00 01 00")
        streams = bytes.fromhex("05 06 07 01")
        tail = bytes.fromhex("00 ff 42")
        single = section(0, 3, tree + b"\x0b") + tail
        four = section(1, 6, tree + jump + streams) + tail
        compare(single, 0, "direct", bytes([0, 1, 1]))
        compare(four, 1, "direct", bytes([0, 1, 1, 0, 1, 1]))
        compare(section(0, 0, tree + b"\x01") + tail, 0, "direct", b"")
        print("Both accepted exact single and four streams, including marker-only streams")

        rejects = (
            (bytes.fromhex("0e 00 00 00"), "truncatedHeader", "truncatedHeader"),
            (section(0, 3, tree + b"\x0b", size=20) + tail, "truncatedBody", "truncatedBody"),
            (section(0, 3, bytes.fromhex("80 00 0b")) + tail, "tree", "zeroMass"),
            (section(0, 3, bytes.fromhex("04 10 3f 02 04 0b")) + tail, "completion", "zeroMass"),
            (section(0, 3, tree + b"\x00") + tail, "single", "badEndMarker"),
            (section(0, 4, tree + b"\x0b") + tail, "single", "incompleteCode"),
            (section(0, 2, tree + b"\x0b") + tail, "single", "trailingBits"),
            (section(1, 6, tree + jump + streams[:-1]) + tail, "four", "invalidStreamExtent"),
            (section(1, 6, tree + jump + streams[:-1] + b"\x00") + tail, "four", "badEndMarker"),
            (section(1, 5, tree + jump + streams) + tail, "four", "invalidRegeneratedSize"),
            (section(0, 3, tree + b"\x0b", kind=3) + tail, "unsupported", "treeless"),
        )
        for wire, stage, reason in rejects:
            result = subprocess.run([native], input=wire, stdout=subprocess.PIPE)
            require(result.returncode == 3, f"native accepted {stage}/{reason}")
            expect_error(work, wire, stage, reason)
        for kind, name in ((0, "raw"), (1, "rle")):
            wire = bytes([8 + kind, 0x61, 0])
            require(run(native, data=wire) == b"2 1\na", f"native {name} source")
            expect_error(work, wire, "unsupported", name)
        expect_error(work, single, "inputLimit", "inputLimit", input_cap=5)
        expect_error(work, four, "outputLimit", "outputLimit", output_cap=5)
        expect_error(work, section(3, 0, b"", size=131072), "inputLimit", "inputLimit", input_cap=262144)
        expect_error(work, section(3, 131073, b""), "outputLimit", "outputLimit", output_cap=262144)
        print("Both rejected 11 malformed or unavailable-state controls")
        print("Lean classified raw and RLE separately and enforced caller and 128 KiB caps")


if __name__ == "__main__":
    main()
