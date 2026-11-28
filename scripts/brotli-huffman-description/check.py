#!/usr/bin/env python3
"""Replay full simple and complex Brotli Huffman descriptions under one bit cap."""
import argparse
from hashlib import sha256
from importlib.metadata import version
import json
from pathlib import Path
import random
import runpy
from tempfile import TemporaryDirectory

import pyarrow as pa

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PHASE_ONE = runpy.run_path(str(ROOT / "scripts/brotli-huffman-code-lengths/check.py"))
PIN = PHASE_ONE["PIN"]
check, run = PHASE_ONE["check"], PHASE_ONE["run"]
SIMPLE_SHAPES = ["singleton", "pair", "triple", "balanced", "skewed"]


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
            tables.append({"alphabet": alphabet, "selector": selector, "start": extent - remaining - 2})
        elif tag == "simple":
            shape, remaining, *symbols = values
            tables[-1].update(shape=SIMPLE_SHAPES[shape], stop=extent - remaining, symbols=symbols)
        elif tag == "main":
            tables[-1].update(shape="complex", stop=extent - values[0])
        elif tag == "codes":
            tables[-1]["codes"] = [[code, width] if width else None
                                   for code, width in zip(values[::2], values[1::2], strict=True)]
        elif tag == "simpleCodes":
            codes = [None] * tables[-1]["alphabet"]
            for ordinal, code, width in zip(values[::3], values[1::3], values[2::3], strict=True):
                check(codes[ordinal] is None, "native simple code uniqueness")
                codes[ordinal] = [code, width]
            tables[-1]["codes"] = codes
        elif tag != "secondary":
            raise ValueError(line)
    for table in tables:
        check(table["alphabet"] == len(table["codes"]), "native table extent")
        if table["selector"] == 1:
            check(sorted(table["symbols"]) == [i for i, code in enumerate(table["codes"]) if code is not None],
                  "native simple symbol ordinals")
        else:
            check(table["shape"] == "complex", "native dispatch")
    return tables


def replay(name, wire, tables, work):
    file, requests = work / "input.br", work / "requests"
    file.write_bytes(wire)
    lines = []
    for table in tables:
        only = table["symbols"][0] if table["shape"] == "singleton" else "-"
        lines.append(f"{table['start']} {table['stop']} {table['alphabet']} {only}\n")
    requests.write_text("".join(lines))
    result = run("lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
                 HERE / "Interop.lean", file, requests)
    check([json.loads(line) for line in result.stdout.decode().splitlines()] ==
          [table["codes"] for table in tables], f"{name}: native code map")
    summary = []
    for table in tables:
        row = {key: value for key, value in table.items() if key != "codes"}
        row["codes_sha256"] = sha256(json.dumps(table["codes"], separators=(",", ":")).encode()).hexdigest()
        summary.append(row)
        print(f"{name}: selector {row['selector']}, {row['shape']}, alphabet {row['alphabet']}, "
              f"bits [{row['start']}, {row['stop']})")
    return {"sha256": sha256(wire).hexdigest(), "tables": summary}


def collect(reference, traced, harness, work):
    inputs = PHASE_ONE["parquet_inputs"](harness, reference, work)
    for name, weights in (("pair", "aaab"), ("triple", "abc"), ("balanced", "abcd"),
                          ("skewed", "aaaaaaaaabbbbccd")):
        generator = random.Random(9)
        text = bytes(ord(generator.choice(weights)) for _ in range(64))
        inputs[f"libbrotli-{name}"] = run(reference, "-q", "4", "-w", "18", "-c", data=text).stdout
    text = b"".join(
        f"Reader {i % 23} checks compressed page {i} with a fixed output budget.\n".encode()
        for i in range(99))
    inputs["libbrotli-text-q4"] = run(reference, "-q", "4", "-w", "18", "-c", data=text).stdout
    observed = {name: replay(name, wire, trace_tables(wire, reference, traced), work)
                for name, wire in inputs.items()}
    tables = [table for fixture in observed.values() for table in fixture["tables"]]
    check({table["selector"] for table in tables} == {0, 1, 2, 3}, "selector coverage")
    check({table["shape"] for table in tables} == set(SIMPLE_SHAPES) | {"complex"}, "shape coverage")
    return observed


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--brotli-source", type=Path)
    args = parser.parse_args()
    check((pa.__version__, version("thrift")) == ("26.0.1", "0.25.0"), "fixture package pins")
    harness = runpy.run_path(str(ROOT / "scripts/parquet-brotli-raw/check.py"))
    check(harness["PIN"] == PIN, "Brotli pin")
    with TemporaryDirectory(prefix="silmaril-brotli-description-") as temp:
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
