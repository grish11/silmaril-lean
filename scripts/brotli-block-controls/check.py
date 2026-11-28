#!/usr/bin/env python3
"""Compare the first compressed meta-block's controls against pinned libbrotli."""
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
PREFIX_ORACLE = runpy.run_path(str(ROOT / "scripts/brotli-huffman-code-lengths/check.py"))
PIN = PREFIX_ORACLE["PIN"]
check, run = PREFIX_ORACLE["check"], PREFIX_ORACLE["run"]


def setup_trace(source, work):
    traced = work / "traced"
    traced.mkdir()
    run("tar", "-x", "-C", traced, data=run("git", "-C", source, "archive", PIN).stdout)
    run("python3", "-I", HERE / "trace-reference.py", traced)
    build = work / "trace-build"
    run("cmake", "-S", traced, "-B", build, "-DCMAKE_BUILD_TYPE=Release", "-DBUILD_TESTING=OFF")
    run("cmake", "--build", build, "--target", "brotli", "--parallel", "4")
    return build / "brotli"


def native_controls(traced, reference, wire):
    result = run(traced, "-d", "-c", data=wire)
    check(result.stdout == run(reference, "-d", "-c", data=wire).stdout, "native decoded output")
    rows = iter(result.stderr.decode().splitlines())
    entries = []
    extent = 8 * len(wire)

    def event(label, category):
        kind, index, value, remain = next(rows).split()
        check(kind == label and int(index) == category, "native control order")
        return int(value), extent - int(remain)

    for category in range(3):
        _, start = event("start", category)
        types, stop = event("types", category)
        if entries:
            check(start == entries[-1]["stop"], "contiguous native controls")
        entry = {"start": start, "types": types}
        if types > 1:
            initial, stop = event("length", category)
            entry["initial_count"] = initial
        entry["stop"] = stop
        entries.append(entry)
    return entries


def compare(work, wire, entries):
    fixture = work / "input.br"
    fixture.write_bytes(wire)
    start, stop = entries[0]["start"], entries[-1]["stop"]
    result = run("lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
                 HERE / "Interop.lean", fixture, str(start), str(stop))
    expected = [[row["types"], row["initial_count"], row["types"] + 2, 26]
                if row["types"] > 1 else [1] for row in entries]
    check(json.loads(result.stdout) == [[row["stop"] for row in entries], *expected],
          "Lean controls or category boundaries differ from native trace")


def collect(reference, traced, harness, work):
    streams = PREFIX_ORACLE["parquet_inputs"](harness, reference, work)
    for name, chunk, quality in (("literal-multiple", 2048, 10), ("distance-multiple", 2048, 9),
                                 ("three-multiple", 8192, 11)):
        generator = random.Random(281)
        plain = b"".join(bytes(65 + 20 * (j % 3) + generator.randrange(j % 3 + 2)
                               for _ in range(chunk)) for j in range(6))
        streams[name] = run(reference, "-q", str(quality), "-w", "18", "-c", data=plain).stdout

    output = {}
    for name, wire in streams.items():
        entries = native_controls(traced, reference, wire)
        compare(work, wire, entries)
        output[name] = {"bytes": len(wire), "sha256": sha256(wire).hexdigest(), "controls": entries}
        print(f"{name}: bits [{entries[0]['start']}, {entries[-1]['stop']}), "
              f"types {[row['types'] for row in entries]}, "
              f"initial counts {[row.get('initial_count') for row in entries]}, exact and one-bit-short caps checked")
    triples = [fixture["controls"] for fixture in output.values()]
    check(any(all(row["types"] > 1 for row in entries) for entries in triples), "multi-type coverage")
    check(any(all(row["types"] == 1 for row in entries) for entries in triples), "single-type coverage")
    return output


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--brotli-source", type=Path)
    args = parser.parse_args()
    check((pa.__version__, version("thrift")) == ("26.0.1", "0.25.0"), "producer versions")
    harness = runpy.run_path(str(ROOT / "scripts/parquet-brotli-raw/check.py"))
    check(harness["PIN"] == PIN, "libbrotli pin")
    with TemporaryDirectory(prefix="silmaril-brotli-controls-") as temp:
        work = Path(temp)
        clean = work / "clean"
        clean.mkdir()
        source = args.brotli_source.resolve() if args.brotli_source else None
        reference = harness["build_reference"](source, clean)
        traced = setup_trace(source or clean / "brotli", work)
        manifest = {"libbrotli_commit": PIN, "fixtures": collect(reference, traced, harness, work)}
        check(manifest == json.loads((HERE / "fixtures.json").read_text()), "fixture hashes and native controls")
        print(f"Fixture manifest matched libbrotli {PIN}, PyArrow {pa.__version__}, Thrift {version('thrift')}")


if __name__ == "__main__":
    main()
