#!/usr/bin/env python3
"""Compare complete block output and state handoffs with pinned libzstd."""
from hashlib import sha256
from pathlib import Path
from runpy import run_path
import subprocess
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
oracle = run_path(str(ROOT / "scripts/zstd-literal-oracle/check.py"))
run, require = oracle["run"], oracle["require"]


def frame(blocks):
    # Dictionary-free frame, no content checksum, 1024-byte window.
    header = bytes.fromhex("28 b5 2f fd 00 00")
    return header + b"".join(
        ((size << 3) | (kind << 1) | (index == len(blocks) - 1)).to_bytes(3, "little") + body
        for index, (kind, size, body) in enumerate(blocks)
    )


def lean(work, steps):
    args = []
    for index, (action, body) in enumerate(steps):
        path = work / f"block-{index}"
        path.write_bytes(body)
        args.append(f"{action}={path}")
    output = run("lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                 "--run", HERE / "Interop.lean", *args)
    decoded = []
    for line in output.splitlines():
        status, fields = line.split(b" ", 1)
        require(status in (b"ok", b"error"), f"unexpected Lean output {line!r}")
        decoded.append(bytes(map(int, fields.split())) if status == b"ok" else fields.decode())
    return decoded


def fixture(native):
    # The first five sections use the pinned Repeat-table oracle's encodings.
    # The last two use a zero-literal Offset_Value 2, selecting the third
    # repeat distance and rotating it to the front (with cross-block copies).
    cases = (
        ("raw literals, fresh tables", "raw", b"abcd", "011802103f0322", b"abcdabc"),
        ("unsequenced RLE literals", "rle", b"!!!", "00", b"!!!"),
        ("RLE literals, all tables repeated", "rle", b"wwww", "01fc0322", b"wwwwwww"),
        ("replace two tables", "raw", b"ABCDE", "016c05108a1f0023", b"ABCDEABC"),
        ("use replacements", "raw", b"vwxyz", "01fc1823", b"vwxyzvwxy"),
        ("physical raw block", "plain", b"ABCD", "", b"ABCD"),
        ("physical RLE block", "plain-rle", b"XX", "", b"XX"),
        ("zero-literal repeat offset", "raw", b"", "015400010302", b"CDXXCD"),
        ("repeat tables and offset again", "raw", b"", "01fc02", b"DXXCDD"),
    )
    for name, kind, literals, sequence_hex, out in cases:
        if kind == "plain":
            block, step = (0, len(literals), literals), ("plain", literals)
        elif kind == "plain-rle":
            block, step = (1, len(literals), literals[:1]), ("plain", literals)
        else:
            body = run(native, kind, data=literals) + bytes.fromhex(sequence_hex)
            block, step = (2, len(body), body), ("decode", body)
        yield name, block, step, out


def main():
    with TemporaryDirectory(prefix="silmaril-zstd-compressed-block-") as directory:
        work = Path(directory)
        native = oracle["build_reference"](work)
        print(f'libzstd v1.5.7 {oracle["PIN"]}')

        native_blocks, steps, expected = [], [], []
        for name, block, step, out in fixture(native):
            native_blocks.append(block)
            steps.append(step)
            expected.append(out)
            print(f"{name}: body={block[2].hex()} bytes={out.hex()}")
        full = frame(native_blocks)
        require(lean(work, steps) == expected, "Lean per-block output or state handoff differs")
        require(run(native, "decode", data=full) == b"".join(expected), "native complete frame differs")
        print(f"Nine-block exact output agreed, frame={sha256(full).hexdigest()}")

        old_repeat = run(native, "raw", data=b"wxyz") + bytes.fromhex("01fc0322")
        for name, corrupt, reason in (
            ("valid replacement prefix, zero marker", "00015400010300", "badEndMarker"),
            ("valid replacement prefix and commands, literal underflow", "00015401000001", "literalUnderflow"),
        ):
            body = bytes.fromhex(corrupt)
            checked = lean(work, [steps[0], ("reject", body), ("decode", old_repeat)])
            require(len(checked) == 3 and isinstance(checked[1], str) and reason in checked[1],
                    f"{name}: wrong Lean result {checked!r}")
            require(checked[0] == expected[0] and checked[2] == b"wxyzwxy",
                    f"{name}: retry must still use the earlier accepted tables")
            rejected = subprocess.run([native, "decode"], input=frame([native_blocks[0], (2, len(body), body)]),
                                      stdout=subprocess.PIPE)
            require(rejected.returncode == 3, f"{name}: native should reject")
            print(f"{name}: both rejected; Lean retry succeeded with prior state")


if __name__ == "__main__":
    main()
