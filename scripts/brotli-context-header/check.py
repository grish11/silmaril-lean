#!/usr/bin/env python3
"""Compare Brotli distance parameters and context modes with pinned native traces."""
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
PREFIX = runpy.run_path(str(ROOT / "scripts/brotli-huffman-code-lengths/check.py"))
PIN = PREFIX["PIN"]
check, run = PREFIX["check"], PREFIX["run"]


def setup_trace(source, work):
    traced = work / "traced"
    traced.mkdir()
    run("tar", "-x", "-C", traced, data=run("git", "-C", source, "archive", PIN).stdout)
    run("python3", "-I", HERE / "trace-reference.py", traced)
    build = work / "trace-build"
    run("cmake", "-S", traced, "-B", build, "-DCMAKE_BUILD_TYPE=Release", "-DBUILD_TESTING=OFF")
    run("cmake", "--build", build, "--target", "brotli", "--parallel", "4")
    return build / "brotli"


def trace(wire, reference, traced):
    native = run(traced, "-d", "-c", data=wire)
    check(native.stdout == run(reference, "-d", "-c", data=wire).stdout, "native decoded bytes")
    rows = iter(native.stderr.decode().splitlines())
    extent = 8 * len(wire)

    def event(label, category):
        kind, ordinal, value, remaining = next(rows).split()
        check(kind == label and int(ordinal) == category, "native control order")
        return int(value), extent - int(remaining)

    counts = []
    for category in range(3):
        _, begin = event("start", category)
        if category == 0:
            start = begin
        types, end = event("types", category)
        counts.append(types)
        if types > 1:
            _, end = event("length", category)
    tag, postfix, direct, remaining, *modes = next(rows).split()
    stop = extent - int(remaining)
    modes = list(map(int, modes))
    check(tag == "context" and len(modes) == counts[0] and stop == end + 6 + 2 * counts[0],
          "native context extent")
    return {"start": start, "post_controls": end, "stop": stop, "types": counts,
            "postfix": int(postfix), "direct": int(direct), "modes": modes}


def ordinary_inputs(reference, harness, work):
    streams = {name: (wire, "PyArrow", None)
               for name, wire in PREFIX["parquet_inputs"](harness, reference, work).items()}

    for name, base, spacing, chunk, seed in (
        ("cli-utf8-multiple", 65, 20, 8192, 281),
        ("cli-signed-multiple", 128, 16, 2048, 917),
    ):
        rng = random.Random(seed)
        plain = b"".join(bytes(base + spacing * (j % 3) + rng.randrange(j % 3 + 2)
                               for _ in range(chunk)) for j in range(6))
        wire = run(reference, "-q", "11", "-w", "18", "-c", data=plain).stdout
        streams[name] = (wire, "libbrotli CLI quality 11", None)

    return streams


def inputs(reference, writer, harness, work):
    streams = ordinary_inputs(reference, harness, work)
    text = b"".join(
        f"Reader {i % 23} checks compressed page {i} with a fixed output budget.\n".encode()
        for i in range(99))
    for postfix, direct in ((0, 15), (1, 12), (2, 60), (3, 120)):
        wire = run(writer, str(postfix), str(direct), data=text).stdout
        streams[f"configured-postfix-{postfix}"] = (wire, "libbrotli encoder API quality 7", (postfix, direct))
    return streams


def collect(reference, traced, writer, harness, work):
    output = {}
    for name, (wire, provenance, configured) in inputs(reference, writer, harness, work).items():
        fields = trace(wire, reference, traced)
        if configured is not None:
            check((fields["postfix"], fields["direct"]) == configured, "native configured parameters")
        fixture = work / "input.br"
        fixture.write_bytes(wire)
        start, mid, stop = (fields[k] for k in ("start", "post_controls", "stop"))
        result = run("lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
                     HERE / "Interop.lean", fixture, str(start), str(mid), str(stop))
        postfix, direct = fields["postfix"], fields["direct"]
        check([json.loads(line) for line in result.stdout.splitlines()] ==
              [[postfix, direct, 16 + direct + 48 * 2 ** postfix], fields["modes"]],
              "Lean fields differ from pinned trace")
        output[name] = {"provenance": provenance, "bytes": len(wire), "sha256": sha256(wire).hexdigest(), **fields}
        print(f"{name}: bits [{start}, {mid}, {stop}), types {fields['types']}, "
              f"NPOSTFIX={postfix}, NDIRECT={direct}, modes={fields['modes']}")
    check({row["postfix"] for row in output.values()} == {0, 1, 2, 3}, "postfix coverage")
    check({mode for row in output.values() for mode in row["modes"]} == {0, 2, 3}, "producer mode coverage")
    return output


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--brotli-source", type=Path)
    args = parser.parse_args()
    check((pa.__version__, version("thrift")) == ("26.0.1", "0.25.0"), "producer versions")
    harness = runpy.run_path(str(ROOT / "scripts/parquet-brotli-raw/check.py"))
    check(harness["PIN"] == PIN, "libbrotli pin")
    with TemporaryDirectory(prefix="silmaril-brotli-context-") as temp:
        work = Path(temp)
        clean = work / "clean"
        clean.mkdir()
        source = args.brotli_source.resolve() if args.brotli_source else None
        reference = harness["build_reference"](source, clean)
        source = source or clean / "brotli"
        traced = setup_trace(source, work)
        writer = work / "parameter-writer"
        native_build = reference.parent
        run("cc", "-Wall", "-Wextra", "-Werror", "-I", source / "c/include", HERE / "parameter-writer.c",
            "-L", native_build, f"-Wl,-rpath,{native_build}", "-lbrotlienc", "-o", writer)
        manifest = {"libbrotli_commit": PIN, "fixtures": collect(reference, traced, writer, harness, work)}
        check(manifest == json.loads((HERE / "fixtures.json").read_text()), "fixture hashes and native fields")
        print(f"Fixture manifest matched libbrotli {PIN}, PyArrow {pa.__version__}, Thrift {version('thrift')}")


if __name__ == "__main__":
    main()
