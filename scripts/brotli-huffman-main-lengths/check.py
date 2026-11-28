#!/usr/bin/env python3
"""Compare complete main Huffman length vectors and cursors with pinned libbrotli."""
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
    run("cmake", "-S", trace, "-B", build, "-DCMAKE_BUILD_TYPE=Release",
        "-DBUILD_TESTING=OFF", "-DBUILD_SHARED_LIBS=OFF")
    run("cmake", "--build", build, "--target", "brotli", "--parallel", "4")
    writer = work / "singleton-writer"
    run("cc", "-I", trace, "-I", trace / "c/include", HERE / "singleton-writer.c",
        build / "libbrotlienc.a", build / "libbrotlicommon.a", "-lm", "-o", writer)
    return build / "brotli", writer


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
        else:
            raise ValueError(line)
    check(all(t["alphabet"] == len(t["lengths"]) for t in tables), "table extent")
    return tables


def replay(name, wire, tables, work):
    file, requests = work / "input.br", work / "requests"
    file.write_bytes(wire)
    requests.write_text("".join(f"{t['header']} {t['start']} {t['stop']} {t['alphabet']}\n" for t in tables))
    result = run("lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
                 HERE / "Interop.lean", file, requests)
    check([json.loads(row) for row in result.stdout.decode().splitlines()] ==
          [t["lengths"] for t in tables], f"{name} main lengths")
    summary = []
    for table in tables:
        lengths = table["lengths"]
        check(sum(32768 >> length for length in lengths if length) == 32768, f"{name} Kraft sum")
        print(f"{name}: {table['alphabet']} lengths, bits [{table['start']}, {table['stop']}) matched")
        row = {key: value for key, value in table.items() if key != "lengths"}
        row["lengths_sha256"] = sha256(bytes(lengths)).hexdigest()
        summary.append(row)
    return {"sha256": sha256(wire).hexdigest(), "tables": summary}


def collect(reference, traced, writer, harness, work):
    candidates = PHASE_ONE["parquet_inputs"](harness, reference, work)
    del candidates["producer-v2-entropy-brotli"]  # This fixture uses simple descriptions.
    text = b"".join(
        f"Reader {i % 23} checks compressed page {i} with a fixed output budget.\n".encode()
        for i in range(99))
    for quality in (4, 6):
        candidates[f"libbrotli-text-q{quality}"] = run(reference, "-q", str(quality), "-w", "18", "-c",
                                                      data=text).stdout
    observed = {name: replay(name, wire, trace_tables(wire, reference, traced), work)
                for name, wire in candidates.items()}
    for mode, alphabet, width, selector, start in (
        ([], 8, 3, 2, 36),
        (["default"], 256, 8, 3, 34),
    ):
        output = run(writer, *mode)
        name = f"libbrotli-singleton-{alphabet}"
        tables = [{"alphabet": alphabet, "selector": selector, "header": 0, "start": start,
                   "stop": int(output.stderr), "lengths": [width] * alphabet}]
        observed[name] = replay(name, output.stdout, tables, work)
    return observed


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--brotli-source", type=Path)
    args = parser.parse_args()
    check((pa.__version__, version("thrift")) == ("26.0.1", "0.25.0"), "fixture package pins")
    harness = runpy.run_path(str(ROOT / "scripts/parquet-brotli-raw/check.py"))
    check(harness["PIN"] == PIN, "Brotli pin")
    with TemporaryDirectory(prefix="silmaril-brotli-main-") as name:
        work = Path(name)
        clean = work / "clean"
        clean.mkdir()
        source = args.brotli_source.resolve() if args.brotli_source else None
        reference = harness["build_reference"](source, clean)
        traced, writer = setup_trace(source or clean / "brotli", work)
        observed = collect(reference, traced, writer, harness, work)
        pinned = json.loads((HERE / "fixtures.json").read_text())
        check(pinned == {"libbrotli_commit": PIN, "fixtures": observed}, "fixture manifest")
        print(f"Fixture manifest matched libbrotli {PIN}, PyArrow {pa.__version__}, Thrift {version('thrift')}")


if __name__ == "__main__":
    main()
