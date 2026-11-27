#!/usr/bin/env python3
"""Check context maps and exact cursor boundaries on pinned producer streams."""
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
HEADER = runpy.run_path(str(ROOT / "scripts/brotli-context-header/check.py"))
PIN, check, run = HEADER["PIN"], HEADER["check"], HEADER["run"]


def setup_trace(source, work, script=HERE / "trace-reference.py"):
    traced = work / "traced"
    traced.mkdir()
    run("tar", "-x", "-C", traced, data=run("git", "-C", source, "archive", PIN).stdout)
    run("python3", "-I", script, traced)
    build = work / "trace-build"
    run("cmake", "-S", traced, "-B", build, "-DCMAKE_BUILD_TYPE=Release", "-DBUILD_TESTING=OFF")
    run("cmake", "--build", build, "--target", "brotli", "--parallel", "4")
    return build / "brotli"


def native_trace(wire, reference, traced):
    native = run(traced, "-d", "-c", data=wire)
    check(native.stdout == run(reference, "-d", "-c", data=wire).stdout, "native output")
    return native.stderr.decode().splitlines()


def trace(wire, reference, traced, full):
    return parse_maps(wire, native_trace(wire, reference, traced), full)


def parse_maps(wire, records, full):
    lines = iter(records)
    extent = 8 * len(wire)
    first = next(lines).split()
    check(first[:2] == ["start", "0"], "native header start")
    start_controls = extent - int(first[-1])
    context = next(row.split() for row in lines if row.startswith("context "))
    post_modes = extent - int(context[3])
    maps = []
    for kind, contexts in (("literal", 64), ("distance", 4)):
        tag, category, size, remaining = next(lines).split()
        check((tag, category) == ("begin", kind), "native map order")
        size = int(size)
        check(size % contexts == 0, "native map extent")
        row = {"kind": kind, "entries": size, "types": size // contexts, "start": extent - int(remaining)}
        tag, trees, remaining = next(lines).split()
        check(tag == "trees", "native tree count")
        row.update(trees=int(trees), stop=extent - int(remaining))
        if row["trees"] > 1:
            tag, rle = next(lines).split()
            check(tag == "rle", "native RLE flag")
            tag, remaining = next(lines).split()
            check(tag == "symbols", "native map symbol boundary")
            row.update(rle=int(rle), stop=extent - int(remaining))
        work = 0
        record = next(lines).split()
        while record[0] == "token":
            work += 1
            record = next(lines).split()
        tag, flag, end, values = record
        check(tag == "map", "native full map boundary")
        if full:
            row.update(end=extent - int(end), imtf=int(flag), work=work, values=values)
            check(len(bytes.fromhex(values)) == size, "native map output extent")
        maps.append(row)
    check(maps[0]["start"] == post_modes, "native literal map follows the mode vector")
    return start_controls, maps


def collect(reference, traced, harness, work, full):
    # Reuse the immediately preceding header's ordinary producers. Its
    # configured streams exercise distance fields, so they are left out.
    sources = HEADER["ordinary_inputs"](reference, harness, work)
    output = {}
    for name, (wire, provenance, _) in sources.items():
        start_controls, maps = trace(wire, reference, traced, full)
        file, requests = work / "wire.br", work / "requests"
        file.write_bytes(wire)
        if full:
            check(maps[0]["end"] == maps[1]["start"], "native adjacent maps")
            requests.write_text("".join(
                f"{m['kind']} {m['start']} {m['end']} {m['types']} {m['work']}\n" for m in maps))
            expected = [[m["trees"], *bytes.fromhex(m["values"])] for m in maps]
        else:
            requests.write_text("".join(
                f"{m['kind']} {m['start']} {m['stop']} {m['types']}\n" for m in maps))
            expected = [[m["entries"], m["trees"], m["rle"], m["trees"] + m["rle"]]
                        if m["trees"] > 1 else [m["entries"], 1] for m in maps]
        driver = "FullInterop.lean" if full else "Interop.lean"
        result = run("lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
                     HERE / driver, file, str(start_controls), requests)
        check([json.loads(line) for line in result.stdout.splitlines()] == expected, "Lean map result")
        output[name] = {"provenance": provenance, "sha256": sha256(wire).hexdigest(),
                        "start_controls": start_controls, "maps": maps}
        for m in maps:
            if full:
                print(f"{name}: {m['kind']} bits [{m['start']}, {m['end']}), "
                      f"{m['entries']} entries, {m['work']} symbols, IMTF={m['imtf']}")
                continue
            print(f"{name}: {m['kind']} bits [{m['start']}, {m['stop']}), {m['entries']} entries, "
                  f"{m['trees']} trees, RLEMAX={m.get('rle')}")
    check(any(all(m["trees"] == 1 for m in row["maps"]) for row in output.values()), "implicit pair")
    check(any(all(m["trees"] > 1 for m in row["maps"]) for row in output.values()), "coded pair")
    if full:
        flags = {m["imtf"] for row in output.values() for m in row["maps"]}
        check({-1, 1} <= flags, "implicit and inverse transform fixtures")
    return output


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--brotli-source", type=Path)
    parser.add_argument("--full", action="store_true", help="check full maps instead of prefixes")
    args = parser.parse_args()
    check((pa.__version__, version("thrift")) == ("26.0.1", "0.25.0"), "producer versions")
    harness = runpy.run_path(str(ROOT / "scripts/parquet-brotli-raw/check.py"))
    check(harness["PIN"] == PIN, "libbrotli pin")
    with TemporaryDirectory(prefix="silmaril-brotli-context-maps-") as temp:
        work = Path(temp)
        clean = work / "clean"
        clean.mkdir()
        source = args.brotli_source.resolve() if args.brotli_source else None
        reference = harness["build_reference"](source, clean)
        traced = setup_trace(source or clean / "brotli", work)
        manifest = {"libbrotli_commit": PIN, "fixtures": collect(reference, traced, harness, work, args.full)}
        expected = HERE / ("full-fixtures.json" if args.full else "fixtures.json")
        check(manifest == json.loads(expected.read_text()), "fixture pin")
        print(f"Fixture manifest matched libbrotli {PIN}, PyArrow {pa.__version__}, Thrift {version('thrift')}")


if __name__ == "__main__":
    main()
