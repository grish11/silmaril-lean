#!/usr/bin/env python3
"""Compare carried sequence tables and a five-block frame with pinned libzstd."""
from hashlib import sha256
from pathlib import Path
from runpy import run_path
import subprocess
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
TABLE_ORACLE = ROOT / "scripts/zstd-sequence-table-oracle"
tables = run_path(str(TABLE_ORACLE / "check.py"))
sequences = run_path(str(ROOT / "scripts/zstd-sequence-decode-oracle/check.py"))
run, require, bitstream, tables_from = (
    tables[name] for name in ("run", "require", "bitstream", "tables_from")
)


def packet(sections):
    return b"".join(len(section).to_bytes(4, "little") + section for section in sections)


def frame(blocks):
    header = bytes.fromhex("28 b5 2f fd 00 38")  # no dictionary, 128 KiB window
    return header + b"".join(
        ((len(body) << 3) | 4 | (index == len(blocks) - 1)).to_bytes(3, "little") + body
        for index, body in enumerate(blocks)
    )


def groups(output):
    return output.rstrip(b"\n").split(b"\n\n")


def lean(work, sections):
    files = []
    for index, section in enumerate(sections):
        path = work / f"section-{index}"
        path.write_bytes(section)
        files.append(path)
    return subprocess.run(
        ["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
         HERE / "Interop.lean", *files],
        cwd=ROOT, stdout=subprocess.PIPE,
    )


def main():
    with TemporaryDirectory(prefix="silmaril-zstd-repeat-tables-") as directory:
        work = Path(directory)
        zstd = tables["oracle"]["build_reference"](work)
        library = work / "zstd/lib"
        native, ncount = work / "seq-header", work / "ncount"
        run("cc", "-std=c11", "-O2", "-Wall", "-Wextra", "-Werror", "-I", library,
            TABLE_ORACLE / "reference.c", library / "libzstd.a", "-o", native)
        run("cc", "-std=c11", "-O2", "-I", library, ROOT / "scripts/zstd-ncount-oracle/reference.c",
            library / "libzstd.a", "-o", ncount)
        print(f'libzstd v1.5.7 {tables["PIN"]}')

        match_counts = run(ncount, "write", "5", "16", "16")
        offset_counts = run(ncount, "write", "5", "0", "0", "16", "16")
        # Table modes in literal length, offset, match length order.
        plan = (
            ("establish predefined/RLE/transmitted", bytes.fromhex("01 18 02") + match_counts,
             b"abcd", (4, 0), (1, 2), (3, 0), 4),
            ("empty section", b"\0", b"!", (), (), (), 0),
            ("repeat all after empty", bytes.fromhex("01 fc"), b"wxyz", (4, 0), (1, 2), (3, 0), 4),
            ("replace literal and offset, retain match", bytes.fromhex("01 6c 05") + offset_counts,
             b"ABCDE", (5, 0), (5, 3), (3, 0), 5),
            ("repeat all after replacements", bytes.fromhex("01 fc"), b"vwxyz", (5, 0), (5, 3), (4, 0), 5),
        )
        sections, block_bodies, expected_output, table_history, suffixes = [], [], [], [], []
        for name, prefix, literals, literal_code, offset_code, match_code, distance in plan:
            stream = b""
            if distance:
                # Independently select native initial states using the fixture's requested codes.
                output = run(native, "--series", data=packet(sections + [prefix + b"\x01"]))
                consumed, count, chosen = tables_from(groups(output)[-1])
                require((consumed, count) == (len(prefix), 1), f"{name}: native prefix boundary")
                initial = [
                    (next(i for i, row in enumerate(rows) if row[2:] == code), log)
                    for (log, rows), code in zip(chosen, (literal_code, offset_code, match_code))
                ]
                stream = bitstream(initial + [(distance - offset_code[0], offset_code[1])])
                commands = [(len(literals), distance + 3, match_code[0])]
                output = sequences["execute"](literals, commands)
                table_history.append(chosen)
            else:
                output = literals
            sections.append(prefix + stream)
            suffixes.append(stream)
            block_bodies.append(run(zstd, "raw", data=literals) + sections[-1])
            expected_output.append(output)
            print(f"{name}: suffix={stream.hex()} section={sections[-1].hex()}")

        established, after_empty, replaced, after_replacement = table_history
        require(after_empty == established, "empty section must preserve the tables")
        require(replaced[0] != established[0] and replaced[1] != established[1] and
                replaced[2] == established[2], "only the selected alphabets must change")
        require(after_replacement == replaced, "Repeat must select the latest accepted tables")

        native_results = groups(run(native, "--series", data=packet(sections)))
        checked = lean(work, sections)
        require(checked.returncode == 0, f"Lean rejected the series: {checked.stdout!r}")
        observed = groups(checked.stdout)
        require(len(observed) == len(native_results) == len(sections), "one result per block")
        for actual, expected, suffix in zip(observed, native_results, suffixes):
            table_output, suffix_output = actual.rsplit(b"\n", 1)
            require(table_output == expected, "consumed extent or native table rows differ")
            require(suffix_output.removeprefix(b"suffix ").split() == [str(byte).encode() for byte in suffix],
                    "Lean preserved the exact reverse suffix")
        full = frame(block_bodies)
        require(run(zstd, "decode", data=full) == b"".join(expected_output), "native full-frame output")
        print(f"Five-block frame: exact prefixes, suffixes and table rows agreed, frame={sha256(full).hexdigest()}")

        for label, mode in (("literalLength", 0xc0), ("offset", 0x30), ("matchLength", 0x0c)):
            fresh_repeat = bytes((1, mode, 1))
            for leading_zero in (False, True):
                partial = ([b"\0"] if leading_zero else []) + [fresh_repeat]
                checked = lean(work, partial)
                require(checked.returncode == 3 and
                        b"missingTable" in checked.stdout and label.encode() in checked.stdout, f"expected missing {label}: {checked.stdout!r}")
                native_result = subprocess.run([native, "--series"], input=packet(partial),
                                               stdout=subprocess.PIPE)
                require(native_result.returncode == 3, f"native accepted unseeded {label}")
            print(f"Unseeded {label} Repeat rejected, including after a leading empty section")

        unseeded = frame([bytes.fromhex("20 61 62 63 64 01 fc 01")])
        native_result = subprocess.run([zstd, "decode"], input=unseeded, stdout=subprocess.PIPE)
        require(native_result.returncode == 3, "native full-frame Repeat without a prior table")


if __name__ == "__main__":
    main()
