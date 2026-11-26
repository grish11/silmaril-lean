#!/usr/bin/env python3
"""Test decoded commands against independent libzstd table-driven fixtures."""
from hashlib import sha256
from pathlib import Path
from runpy import run_path
import subprocess
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
TABLE_ORACLE = ROOT / "scripts/zstd-sequence-table-oracle"
oracle = run_path(str(TABLE_ORACLE / "check.py"))
frames = oracle["oracle"]
bitstream, tables_from, run, require, frame = (
    oracle[name] for name in ("bitstream", "tables_from", "run", "require", "frame")
)


def lean(work, data, byte_cap=None, seq_cap=2):
    source = work / "section"
    source.write_bytes(data)
    result = subprocess.run(
        ["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
         HERE / "Interop.lean", source, str(len(data) if byte_cap is None else byte_cap), str(seq_cap)],
        cwd=ROOT, stdout=subprocess.PIPE, text=True,
    )
    if result.returncode == 3:
        return result.stdout.strip()
    result.check_returncode()
    return [tuple(map(int, line.split())) for line in result.stdout.splitlines()]


def two_states(table, targets):
    """Find a native state whose transition interval reaches the second code."""
    log, rows = table
    for state, (baseline, width, base, extra) in enumerate(rows):
        if (base, extra) != targets[0]:
            continue
        for step in range(1 << width):
            if rows[baseline + step][2:] == targets[1]:
                return (state, log), (step, width)
    raise SystemExit(f"no native path for {targets}")


def fixture(native, ncount, modes, symbols, codes, extras):
    # symbols, codes and extras are given in LL, OF, ML order.
    count = 2
    ll, ofc, ml = modes
    prefix = bytes((count, 64 * ll + 16 * ofc + 4 * ml))
    for mode, (first, last) in zip(modes, symbols):
        if mode == 1:
            require(first == last, "RLE requires one symbol")
            prefix += bytes([first])
        elif mode == 2:
            require(first != last, "transmitted table needs two symbols")
            weights = [16 if symbol in (first, last) else 0 for symbol in range(max(first, last) + 1)]
            prefix += run(ncount, "write", "5", *map(str, weights))

    used, actual_count, tables = tables_from(run(native, data=prefix + b"\x01"))
    require((used, actual_count) == (len(prefix), count), "unexpected native prefix")
    states = [two_states(table, targets) for table, targets in zip(tables, codes)]
    initial = [state for state, _ in states]
    updates = [states[index][1] for index in (0, 2, 1)]
    payloads = [
        [(extras[index][command], codes[index][command][1]) for index in (1, 2, 0)]
        for command in range(count)
    ]
    return prefix, initial, updates, payloads


def execute(literals, commands):
    """Simple independent match copy for these fixtures' explicit offsets."""
    output = bytearray()
    consumed = 0
    for literal_length, offset_value, match_length in commands:
        end = consumed + literal_length
        require(end <= len(literals), "literal count exceeds fixture")
        output += literals[consumed:end]
        consumed = end
        distance = offset_value - 3
        require(0 < distance <= len(output), "fixture offset outside history")
        for _ in range(match_length):
            output.append(output[-distance])
    return bytes(output + literals[consumed:])


def main():
    with TemporaryDirectory(prefix="silmaril-zstd-sequence-decode-") as directory:
        work = Path(directory)
        decoder = frames["build_reference"](work)
        library = work / "zstd/lib"
        native, counts = work / "seq-header", work / "ncount"
        run("cc", "-std=c11", "-O2", "-Wall", "-Wextra", "-Werror", "-I", library,
            TABLE_ORACLE / "reference.c", library / "libzstd.a", "-o", native)
        run("cc", "-std=c11", "-O2", "-I", library, ROOT / "scripts/zstd-ncount-oracle/reference.c",
            library / "libzstd.a", "-o", counts)
        print(f'libzstd v1.5.7 {oracle["PIN"]}')

        # Offset table rows use libzstd's already-adjusted base (Offset_Value - 3).
        # The independent expectations below are raw (LL, Offset_Value, ML).
        cases = (
            ((0, 1, 2), ((16, 17), (3, 3), (32, 33)), ((1, 0), (5, 2), (0, 1)),
             [(17, 13, 35), (18, 10, 38)]),
            ((2, 0, 1), ((16, 17), (3, 2), (32, 32)), ((1, 0), (5, 2), (0, 1)),
             [(17, 13, 35), (18, 6, 36)]),
            ((1, 2, 0), ((16, 16), (3, 2), (32, 33)), ((1, 0), (5, 2), (0, 1)),
             [(17, 13, 35), (16, 6, 38)]),
            ((0, 2, 2), ((16, 17), (3, 2), (32, 33)), ((1, 0), (5, 2), (0, 1)),
             [(17, 13, 35), (18, 6, 38)]),
        )
        maps = ({16: (16, 1), 17: (18, 1)}, {2: (1, 2), 3: (5, 3)}, {32: (35, 1), 33: (37, 1)})
        for modes, symbols, extras, expected in cases:
            codes = tuple(tuple(mapping[symbol] for symbol in pair) for mapping, pair in zip(maps, symbols))
            prefix, initial, updates, payloads = fixture(native, counts, modes, symbols, codes, extras)
            require(all(width > 0 for (_, width), mode in zip(updates, (modes[0], modes[2], modes[1]))
                        if mode != 1), "every FSE table must consume a transition field")
            fields = initial + payloads[0] + updates + payloads[1]
            section = prefix + bitstream(fields)
            literals = bytes(range(sum(command[0] for command in expected))) + b"TAIL"
            literal_wire = run(decoder, "raw", data=literals)
            full = frame(literal_wire + section)
            require(lean(work, section) == expected, f"{modes}: raw commands")
            require(run(decoder, "decode", data=full) == execute(literals, expected),
                    f"{modes}: independent command execution differs from libzstd")
            print(f"{modes}: {expected}, updates={updates}, section={section.hex()}, "
                  f"frame={sha256(full).hexdigest()}")

        # Underflow vectors preserve the exact preceding reads and then end.
        malformed = (
            ("missing bitstream", prefix, "missingBitstream"),
            ("zero marker", prefix + b"\0", "badEndMarker"),
            ("initial state underflow", prefix + bitstream(initial[:1]), "bitUnderflow"),
            ("extra field underflow", prefix + bitstream(initial + payloads[0][:1]), "bitUnderflow"),
            ("transition field underflow", prefix + bitstream(initial + payloads[0] + updates[:1]),
             "bitUnderflow"),
            ("last command underflow", prefix + bitstream(fields[:-1]), "bitUnderflow"),
            ("extra payload bit", prefix + bitstream(fields + [(0, 1)]), "trailingBits"),
        )
        for name, wire, reason in malformed:
            failure = lean(work, wire)
            require(isinstance(failure, str) and reason in failure, f"{name}: {failure!r}")
            native_result = subprocess.run([decoder, "decode"], input=frame(literal_wire + wire),
                                           stdout=subprocess.PIPE)
            require(native_result.returncode == 3, f"{name}: expected native rejection")
            print(f"{name}: Lean {reason}, libzstd rejected")

        for byte_cap, seq_cap, reason in ((len(section) - 1, 2, "inputLimit"),
                                         (len(section), 1, "sequenceLimit")):
            failure = lean(work, section, byte_cap, seq_cap)
            require(isinstance(failure, str) and reason in failure, f"expected {reason}: {failure!r}")
        require(lean(work, b"\x00") == [], "zero sequences")
        print("Both caller caps rejected; zero count produced no commands")


if __name__ == "__main__":
    main()
