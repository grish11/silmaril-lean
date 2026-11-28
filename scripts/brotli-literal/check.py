#!/usr/bin/env python3
"""Check RFC literal contexts and first-command insertions against libbrotli."""
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
SCRIPTS = HERE.parent
MAPS = runpy.run_path(str(SCRIPTS / "brotli-context-maps/check.py"))
PIN, check, run = MAPS["PIN"], MAPS["check"], MAPS["run"]


def lean(*args):
    return run("lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
               "--run", HERE / "Interop.lean", *args).stdout


def context_fingerprint(source, work):
    tool = work / "contexts"
    output = work / "contexts.bin"
    run("cc", "-std=c99", "-Wall", "-Wextra", "-Werror", "-I", source, "-I", source / "c/include",
        HERE / "context.c", source / "c/common/context.c", "-o", tool)
    native = run(tool).stdout
    lean("--contexts", output)
    check(len(native) == 4 * 256 * 256 and native == output.read_bytes(), "all RFC context IDs")
    return sha256(native).hexdigest()


def debruijn_pairs(alphabet):
    # Rotate through every ordered pair once. A long literal-only input
    # helps test the final command with an advertised but unused copy.
    out = []
    for i, first in enumerate(alphabet):
        out.append(first)
        for second in alphabet[i + 1:]:
            out.extend((first, second))
    return bytes(out)


def inputs(reference, harness, work):
    for name, wire in MAPS["HEADER"]["PREFIX"]["parquet_inputs"](harness, reference, work).items():
        yield name, wire, "PyArrow", None

    for name, alphabets, quality in (
        ("cli-alternating-case", [b"ABCDEFGHIJKLMNOPQRSTUVWXYZ", b"abcdefghijklmnopqrstuvwxyz"], 11),
        ("cli-signed", [b"\x00\x01\x02\x03", b"\x80\x90\xa0\xf0", b"\xf0\xf1\xf2\xf3"], 10),
    ):
        rng = random.Random(281)
        data = bytes(rng.choice(alphabets[i % len(alphabets)]) for i in range(2048))
        wire = run(reference, "-q", str(quality), "-w", "18", "-c", data=data).stdout
        yield name, wire, f"libbrotli CLI quality {quality}", data

    data = debruijn_pairs(b"abcdefghijklmnop")
    wire = run(reference, "-q", "4", "-w", "18", "-c", data=data).stdout
    yield "cli-literal-only", wire, "libbrotli CLI quality 4", data


def observe(wire, reference, traced, plaintext):
    native = run(traced, "-d", "-c", data=wire)
    check(native.stdout == run(reference, "-d", "-c", data=wire).stdout, "native output")
    if plaintext is not None:
        check(native.stdout == plaintext, "native round trip")
    rows = native.stderr.decode().splitlines()
    extent = 8 * len(wire)
    start = extent - int(next(row.split()[-1] for row in rows if row.startswith("start 0 ")))
    payload = extent - int(next(row.split()[1] for row in rows if row.startswith("payload ")))
    literals, commands, trees, mode, length = map(int, next(
        row.split()[1:] for row in rows if row.startswith("literal_header ")))
    check((literals, commands) == (1, 1), "native single-type fixture")
    first = next(i for i, row in enumerate(rows) if row.startswith("command "))
    kind, symbol, insert, copy, distance, before, after = map(int, rows[first].split()[1:])
    check(kind == 0 and payload == extent - before and insert > 0, "native first command")
    stop = next(i for i in range(first + 1, len(rows)) if rows[i].startswith("literal_end "))
    end, remaining = map(int, rows[stop].split()[1:])
    steps = []
    for row in rows[first + 1:stop]:
        if row.startswith("literal "):
            *fields, beg, fin = map(int, row.split()[1:])
            steps.append([*fields, extent - beg, extent - fin])
    data = native.stdout[:insert]
    check(len(data) == insert and remaining == length - insert, "native insertion length")
    if steps:
        check(len(steps) == insert and bytes(row[4] for row in steps) == data, "native context trace bytes")
    else:
        check(trees == 1, "native fast-path tree")
    history = ([0, 0] + list(data))[-2:][::-1]
    return {"start": start, "payload": payload, "meta_length": length, "mode": mode, "trees": trees,
            "command": [symbol, insert, copy, distance], "begin": extent - after, "end": extent - end,
            "bytes": list(data), "history": history, "done": remaining == 0, "steps": steps}


def collect(source, reference, traced, harness, work):
    contexts = context_fingerprint(source, work)
    fixtures = {}
    for name, wire, provenance, plain in inputs(reference, harness, work):
        expected = observe(wire, reference, traced, plain)
        path = work / "wire.br"
        path.write_bytes(wire)
        actual = json.loads(lean(path))
        native_steps = expected.pop("steps")
        lean_steps = actual.pop("steps")
        check(actual == expected, f"{name}: literal bytes, cursor or history")
        if native_steps:
            check(lean_steps == native_steps, f"{name}: native context and tree selections")
        selected = sorted({row[3] for row in lean_steps})
        data = bytes(expected.pop("bytes"))
        trace = json.dumps(native_steps, separators=(",", ":")).encode()
        fixtures[name] = {"provenance": provenance, "wire_sha256": sha256(wire).hexdigest(),
                          "literal_sha256": sha256(data).hexdigest(), "trace_sha256": sha256(trace).hexdigest(),
                          **expected, "selected": selected}
        print(f"{name}: {len(data)} literals at [{expected['begin']}, {expected['end']}), "
              f"mode {expected['mode']}, trees {selected}, terminal={expected['done']}")
    check({f["mode"] for f in fixtures.values() if len(f["selected"]) > 1} == {2, 3},
          "native UTF-8 and Signed tree selection")
    check(fixtures["cli-literal-only"]["done"] and fixtures["cli-literal-only"]["command"][-1] == 1,
          "native literal-only final command with explicit distance mode")
    return {"libbrotli_commit": PIN, "contexts_sha256": contexts, "fixtures": fixtures}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--brotli-source", type=Path)
    args = parser.parse_args()
    check((pa.__version__, version("thrift")) == ("26.0.1", "0.25.0"), "producer versions")
    harness = runpy.run_path(str(SCRIPTS / "parquet-brotli-raw/check.py"))
    check(harness["PIN"] == PIN, "libbrotli pin")
    with TemporaryDirectory(prefix="silmaril-brotli-literal-") as temp:
        work = Path(temp)
        clean = work / "clean"
        clean.mkdir()
        source = args.brotli_source.resolve() if args.brotli_source else None
        reference = harness["build_reference"](source, clean)
        source = source or clean / "brotli"
        traced = MAPS["setup_trace"](source, work, HERE / "trace-reference.py")
        manifest = collect(source, reference, traced, harness, work)
        check(manifest == json.loads((HERE / "fixtures.json").read_text()), "context and insertion pins")
        print(f"262144 context IDs and fixture manifest matched libbrotli {PIN}, "
              f"PyArrow {pa.__version__}, Thrift {version('thrift')}")


if __name__ == "__main__":
    main()
