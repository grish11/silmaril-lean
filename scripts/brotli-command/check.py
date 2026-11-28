#!/usr/bin/env python3
"""Compare the 704 RFC command rows and naturally compressed command traces."""
import argparse
from hashlib import sha256
from importlib.metadata import version
import json
from pathlib import Path
import runpy
from tempfile import TemporaryDirectory

import pyarrow as pa

HERE = Path(__file__).resolve().parent
SCRIPTS = HERE.parent
MAPS = runpy.run_path(str(SCRIPTS / "brotli-context-maps/check.py"))
PIN, check, run = MAPS["PIN"], MAPS["check"], MAPS["run"]


def lean(*args):
    result = run("lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                 "--run", HERE / "Interop.lean", *args)
    return [json.loads(row) for row in result.stdout.splitlines()]


def fingerprint(data):
    return sha256(json.dumps(data, separators=(",", ":")).encode()).hexdigest()


def check_lut(source, work):
    tool = work / "lut"
    run("cc", "-std=c99", "-Wall", "-Wextra", "-Werror", "-I", source, "-I", source / "c/include",
        HERE / "lut.c", source / "c/dec/prefix.c", "-o", tool)
    rows = [list(map(int, row.split())) for row in run(tool).stdout.splitlines()]
    check([row[0] for row in rows] == list(range(704)), "native LUT ordinals")
    check(rows == lean("--lut"), "all command lookup rows")
    return rows


def native_commands(wire, reference, traced):
    records = MAPS["native_trace"](wire, reference, traced)
    extent = 8 * len(wire)
    start = extent - int(next(row.split()[-1] for row in records if row.startswith("start 0 ")))
    types = int(next(row.split()[2] for row in records if row.startswith("types 1 ")))
    payloads = [extent - int(row.split()[1]) for row in records if row.startswith("payload ")]
    check(len(payloads) == 1, "single compressed meta-block in native fixture")
    commands = []
    for row in records:
        if row.startswith("command "):
            category, symbol, insert, copy, mode, begin, end = map(int, row.split()[1:])
            commands.append([category, symbol, insert, copy, mode, extent - begin, extent - end])
    check(commands and commands[0][-2] == payloads[0], "first command and native payload boundary")
    return start, payloads[0], types, commands


def collect(source, reference, traced, harness, work):
    lut = check_lut(source, work)
    output = {}
    coverage = set()
    for name, (wire, provenance, _) in MAPS["HEADER"]["ordinary_inputs"](reference, harness, work).items():
        start, payload, types, commands = native_commands(wire, reference, traced)
        source_file = work / "wire.br"
        source_file.write_bytes(wire)
        requests = work / "commands.txt"
        requests.write_text("".join(f"{category} {begin} {end}\n" for category, *_, begin, end in commands))
        check(lean(source_file, requests, str(start), str(payload), str(types)) == commands, f"{name}: native command values or cursors")
        for _, symbol, _, _, mode, _, _ in commands:
            row = lut[symbol]
            check(row[-1] == mode, "native distance mode")
            coverage.add((mode, row[2] > 0, row[4] > 0))
        implicit = sum(row[4] == 0 for row in commands)
        output[name] = {
            "provenance": provenance, "wire_sha256": sha256(wire).hexdigest(),
            "trace_sha256": fingerprint(commands), "start": start, "payload": payload,
            "types": types, "commands": len(commands), "implicit": implicit,
            "first": commands[0], "last": commands[-1],
        }
        print(f"{name}: {len(commands)} commands, {implicit} implicit, {types} command block types")
    check({x[0] for x in coverage} == {0, 1}, "both distance modes")
    check(any(insert and copy for _, insert, copy in coverage), "both nonzero extras in a command")
    check({row["types"] for row in output.values()} == {1, 2}, "single and selected multi-type paths")
    return {"libbrotli_commit": PIN, "lut_sha256": fingerprint(lut), "fixtures": output}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--brotli-source", type=Path)
    args = parser.parse_args()
    check((pa.__version__, version("thrift")) == ("26.0.1", "0.25.0"), "producer versions")
    harness = runpy.run_path(str(SCRIPTS / "parquet-brotli-raw/check.py"))
    check(harness["PIN"] == PIN, "libbrotli pin")
    with TemporaryDirectory(prefix="silmaril-brotli-command-") as temp:
        work = Path(temp)
        clean = work / "clean"
        clean.mkdir()
        source = args.brotli_source.resolve() if args.brotli_source else None
        reference = harness["build_reference"](source, clean)
        source = source or clean / "brotli"
        traced = MAPS["setup_trace"](source, work, HERE / "trace-reference.py")
        manifest = collect(source, reference, traced, harness, work)
        check(manifest == json.loads((HERE / "fixtures.json").read_text()), "fixture and lookup pins")
        print(f"Fixture manifest and 704 lookup rows matched libbrotli {PIN}, PyArrow {pa.__version__}, Thrift {version('thrift')}")


if __name__ == "__main__":
    main()
