#!/usr/bin/env python3
"""Compare installed code assignments directly with pinned native Brotli tables."""
import argparse
from hashlib import sha256
from importlib.metadata import version
import json
from pathlib import Path
import runpy
from tempfile import TemporaryDirectory

import pyarrow as pa

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PHASE_ONE = runpy.run_path(str(ROOT / "scripts/brotli-huffman-code-lengths/check.py"))
PIN = PHASE_ONE["PIN"]
check, run = PHASE_ONE["check"], PHASE_ONE["run"]


def setup_trace(source, work):
    trace = work / "traced"
    trace.mkdir()
    run("tar", "-x", "-C", trace, data=run("git", "-C", source, "archive", PIN).stdout)
    run("python3", "-I", HERE / "trace-reference.py", trace)
    build = work / "traced-build"
    run("cmake", "-S", trace, "-B", build, "-DCMAKE_BUILD_TYPE=Release", "-DBUILD_TESTING=OFF")
    run("cmake", "--build", build, "--target", "brotli", "--parallel", "4")
    return build / "brotli"


def trace_tables(wire, reference, traced):
    result = run(traced, "-d", "-c", data=wire)
    check(result.stdout == run(reference, "-d", "-c", data=wire).stdout, "reference output")
    extent = 8 * len(wire)
    tables = []
    for line in result.stderr.decode().splitlines():
        tag, *fields = line.split()
        values = list(map(int, fields))
        if tag == "selector":
            alphabet, selector, remaining = values
            check(selector in (0, 2, 3), "complex fixture")
            tables.append({"alphabet": alphabet, "selector": selector, "header": extent - remaining - 2})
        elif tag == "secondary":
            tables[-1]["start"] = extent - values[0]
        elif tag == "main":
            tables[-1].update(stop=extent - values[0], lengths=values[1:])
        elif tag == "codes":
            tables[-1]["codes"] = [[code, width] if width else None
                                   for code, width in zip(values[::2], values[1::2], strict=True)]
        else:
            raise ValueError(line)
    for table in tables:
        check(table["alphabet"] == len(table["lengths"]) == len(table["codes"]), "native table extent")
        check([code[1] if code else 0 for code in table["codes"]] == table["lengths"], "native widths")
    return tables


def selected(table):
    active = [ordinal for ordinal, row in enumerate(table["codes"]) if row is not None]
    deepest = max(active, key=lambda ordinal: table["codes"][ordinal][1])
    return [(ordinal, *table["codes"][ordinal])
            for ordinal in sorted({active[0], active[len(active) // 2], active[-1], deepest})]


def request(table):
    fields = [str(table[key]) for key in ("header", "start", "stop", "alphabet")]
    for ordinal, word, width in selected(table):
        wire = int(f"{word:0{width}b}"[::-1], 2)
        # Three guard bits before the code, and a recognizable unread suffix.
        input_word = ((wire | (0b101 << width)) << 3) | 0b011
        fields.append(f"{ordinal}:{width}:{input_word}")
    return " ".join(fields) + "\n"


def replay(name, wire, tables, work):
    file, requests = work / "input.br", work / "requests"
    file.write_bytes(wire)
    requests.write_text("".join(request(table) for table in tables))
    result = run("lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
                 HERE / "Interop.lean", file, requests)
    rows = [json.loads(line) for line in result.stdout.decode().splitlines()]
    check(len(rows) == len(tables), "table count")
    summary = []
    for table, row in zip(tables, rows, strict=True):
        lengths, codes = table["lengths"], table["codes"]
        check(row == [lengths, [[ordinal, depth] for ordinal, depth in enumerate(lengths)], codes],
              f"{name}: native ordinal and code mapping")
        selected_codes = selected(table)
        print(f"{name}: {table['alphabet']} ordinals, [{table['start']}, {table['stop']}) main bits, "
              f"{len(selected_codes)} selected decodes")
        item = {key: value for key, value in table.items() if key not in ("lengths", "codes")}
        item["codes_sha256"] = sha256(json.dumps(codes, separators=(",", ":")).encode()).hexdigest()
        item["selected"] = [list(code) for code in selected_codes]
        summary.append(item)
    return {"sha256": sha256(wire).hexdigest(), "tables": summary}


def collect(reference, traced, harness, work):
    sources = PHASE_ONE["parquet_inputs"](harness, reference, work)
    del sources["producer-v2-entropy-brotli"]  # The main-table reader takes a complex description.
    text = b"".join(
        f"Reader {i % 23} checks compressed page {i} with a fixed output budget.\n".encode()
        for i in range(99))
    for quality in (4, 6):
        sources[f"libbrotli-text-q{quality}"] = run(reference, "-q", str(quality), "-w", "18", "-c",
                                                  data=text).stdout
    return {name: replay(name, wire, trace_tables(wire, reference, traced), work)
            for name, wire in sources.items()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--brotli-source", type=Path)
    args = parser.parse_args()
    check((pa.__version__, version("thrift")) == ("26.0.1", "0.25.0"), "fixture package pins")
    harness = runpy.run_path(str(ROOT / "scripts/parquet-brotli-raw/check.py"))
    check(harness["PIN"] == PIN, "Brotli pin")
    with TemporaryDirectory(prefix="silmaril-brotli-main-table-") as temp:
        work = Path(temp)
        clean = work / "clean"
        clean.mkdir()
        source = args.brotli_source.resolve() if args.brotli_source else None
        reference = harness["build_reference"](source, clean)
        traced = setup_trace(source or clean / "brotli", work)
        actual = collect(reference, traced, harness, work)
        expected = json.loads((HERE / "fixtures.json").read_text())
        check(expected == {"libbrotli_commit": PIN, "fixtures": actual}, "fixture manifest")
        print(f"Fixture manifest matched libbrotli {PIN}, PyArrow {pa.__version__}, Thrift {version('thrift')}")


if __name__ == "__main__":
    main()
