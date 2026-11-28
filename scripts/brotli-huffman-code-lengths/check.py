#!/usr/bin/env python3
"""Check exact Brotli §3.5 table prefixes from the pinned native writer and decoder."""
import argparse
from hashlib import sha256
from importlib.metadata import version
import json
from pathlib import Path
import runpy
import subprocess
from tempfile import TemporaryDirectory

import pyarrow as pa
import pyarrow.parquet as pq

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PIN = "028fb5a23661f123017c060daa546b55cf4bde29"


def check(condition, message):
    if not condition:
        raise ValueError(message)


def run(*args, data=None):
    return subprocess.run(args, input=data, capture_output=True, check=True)


def setup_trace(source, work):
    trace = work / "traced"
    trace.mkdir()
    archive = run("git", "-C", source, "archive", PIN).stdout
    run("tar", "-x", "-C", trace, data=archive)
    run("python3", "-I", HERE / "trace-reference.py", trace)
    build = work / "traced-build"
    run("cmake", "-S", trace, "-B", build, "-DCMAKE_BUILD_TYPE=Release",
        "-DBUILD_TESTING=OFF", "-DBUILD_SHARED_LIBS=OFF")
    run("cmake", "--build", build, "--target", "brotli", "--parallel", "4")
    # These encoder sources are unchanged by the decoder instrumentation.
    writer = work / "singleton-writer"
    run("cc", "-I", trace, "-I", trace / "c/include", HERE / "singleton-writer.c",
        build / "libbrotlienc.a", build / "libbrotlicommon.a", "-lm", "-o", writer)
    return build / "brotli", writer


def trace_tables(wire, reference, traced):
    traced_result = run(traced, "-d", "-c", data=wire)
    check(traced_result.stdout == run(reference, "-d", "-c", data=wire).stdout, "traced decoder output")
    total = 8 * len(wire)
    tables = []
    for line in traced_result.stderr.decode().splitlines():
        tag, *fields = line.split()
        values = list(map(int, fields))
        if tag == "selector":
            alphabet, selector, remaining = values
            start = total - remaining - 2
            check(selector in range(4) and start >= 0, "native selector and offset")
            tables.append({"alphabet": alphabet, "selector": selector, "start": start})
        elif tag == "secondary":
            remaining, *depths = values
            check(tables and tables[-1]["selector"] != 1 and "stop" not in tables[-1], "native phase order")
            tables[-1].update(stop=total - remaining, depths=depths)
        else:
            raise ValueError(f"unexpected trace line {line}")
    return tables


def canonical(depths):
    # RFC 7932 §3.2 numerical assignment, independent of the Lean constructor.
    pairs = sorted((width, symbol) for symbol, width in enumerate(depths) if width)
    codes = [None] * len(depths)
    if len(pairs) == 1:
        codes[pairs[0][1]] = [0, 0]
    else:
        value, prev = 0, 0
        for width, symbol in pairs:
            value <<= width - prev
            codes[symbol] = [value, width]
            value += 1
            prev = width
        check(value == 1 << prev, "native table is complete")
    return codes


def replay(name, wire, tables, work):
    file, requests = work / "input.br", work / "requests"
    file.write_bytes(wire)
    requests.write_text("".join(f"{t['start']} {t.get('stop', t['start'])}\n" for t in tables))
    result = run("lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
                 HERE / "Interop.lean", file, requests)
    lines = result.stdout.decode().splitlines()
    check(len(lines) == len(tables), f"{name} table count")
    for table, line in zip(tables, lines, strict=True):
        if table["selector"] == 1:
            check(line == "unsupportedSimple", f"{name}: expected simple grammar rejection")
            print(f"{name}: simple description rejected at bit {table['start']}")
        else:
            expected = [table["depths"], canonical(table["depths"])]
            check(json.loads(line) == expected, f"{name} native lengths and canonical codes")
            print(f"{name}: HSKIP {table['selector']}, bits [{table['start']}, {table['stop']}), "
                  "lengths, codes and suffix matched, one-bit-short limit rejected")


def parquet_inputs(harness, reference, work):
    inputs = {}
    cases = harness["make_cases"](reference, work)
    for name in ("producer-v1-entropy-brotli", "producer-v2-entropy-brotli"):
        file = cases[name][0]
        layout = harness["inspect"](file, pq.ParquetFile(pa.BufferReader(file)))
        start = layout["body_at"] + layout["raw_prefix"]
        inputs[name] = file[start:layout["footer_at"]]
    return inputs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--brotli-source", type=Path)
    args = parser.parse_args()
    check((pa.__version__, version("thrift")) == ("26.0.1", "0.25.0"), "fixture package pins")
    harness = runpy.run_path(str(ROOT / "scripts/parquet-brotli-raw/check.py"))
    check(harness["PIN"] == PIN, "Brotli pin")
    with TemporaryDirectory(prefix="silmaril-brotli-huffman-") as temp:
        work = Path(temp)
        clean = work / "clean"
        clean.mkdir()
        source = args.brotli_source.resolve() if args.brotli_source else None
        reference = harness["build_reference"](source, clean)
        traced, singleton_writer = setup_trace(source or clean / "brotli", work)
        inputs = parquet_inputs(harness, reference, work)
        text = b"".join(
            f"Reader {i % 23} checks compressed page {i} with a fixed output budget.\n".encode()
            for i in range(99))
        for quality in (4, 6):
            inputs[f"libbrotli-text-q{quality}"] = run(reference, "-q", str(quality), "-w", "18", "-c",
                                                     data=text).stdout

        observed = {}
        for name, wire in inputs.items():
            tables = trace_tables(wire, reference, traced)
            replay(name, wire, tables, work)
            observed[name] = {"sha256": sha256(wire).hexdigest(), "tables": tables}
        one = run(singleton_writer)
        name = "libbrotli-singleton-description"
        tables = [{"alphabet": 8, "selector": 2, "start": 0, "stop": int(one.stderr),
                   "depths": [0, 0, 0, 1] + [0] * 14}]
        replay(name, one.stdout, tables, work)
        observed[name] = {"sha256": sha256(one.stdout).hexdigest(), "tables": tables}
        expected = json.loads((HERE / "fixtures.json").read_text())
        check(observed == expected["fixtures"] and expected["libbrotli_commit"] == PIN, "fixture manifest")
        print(f"Fixture manifest matched libbrotli {PIN}, PyArrow {pa.__version__}, Thrift {version('thrift')}")


if __name__ == "__main__":
    main()
