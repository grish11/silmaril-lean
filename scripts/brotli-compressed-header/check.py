#!/usr/bin/env python3
"""Compare a complete compressed header against pinned native decoder traces."""
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


def native_header(wire, reference, traced):
    all_records = MAPS["native_trace"](wire, reference, traced)
    payload_index = next(i for i, row in enumerate(all_records) if row.startswith("payload "))
    records = all_records[:payload_index]
    extent = 8 * len(wire)
    payload = extent - int(all_records[payload_index].split()[1])
    start, maps = MAPS["parse_maps"](wire, [x for x in records if not x.startswith("codes ")], True)
    _, postfix, direct, _, *modes = next(x for x in records if x.startswith("context ")).split()
    types = [int(x.split()[2]) for x in records if x.startswith("types ")]
    check(len(types) == 3 and maps[0]["end"] == maps[1]["start"], "native control and map order")
    initial = {int(category): int(value) for _, category, value, _ in
               (x.split() for x in records if x.startswith("length "))}

    groups = [[], [], []]
    control_codes = {}
    tree_ends = []
    for row in records:
        if not row.startswith("codes "):
            continue
        _, label, category, ordinal, alphabet, remaining, *words = row.split()
        codes = list(map(int, words))
        check(len(codes) % 3 == 0, "native code triples")
        assignments = sorted(codes[i:i + 3] for i in range(0, len(codes), 3))
        check(len({x[0] for x in assignments}) == len(assignments), "native code ordinals")
        table = [int(alphabet), assignments]
        category = int(category)
        if label == "tree":
            check(int(ordinal) == len(groups[category]), "native tree ordinal")
            groups[category].append(table)
            tree_ends.append(extent - int(remaining))
        else:
            control_codes[category, label] = table
    counts = [maps[0]["trees"], types[1], maps[1]["trees"]]
    check(list(map(len, groups)) == counts and tree_ends[-1] == payload, "native groups and payload boundary")
    check(maps[1]["end"] < tree_ends[0] and tree_ends == sorted(set(tree_ends)), "native tree boundaries")

    expected = {
        "controls": [[x, initial[i], control_codes[i, "type"], control_codes[i, "count"]]
                     if x > 1 else [1] for i, x in enumerate(types)],
        "distance": [int(postfix), int(direct)],
        "modes": list(map(int, modes)),
        "maps": [[m["trees"], *bytes.fromhex(m["values"])] for m in maps],
        "groups": groups,
        "payload": payload,
    }
    return start, maps, counts, expected


def collect(source, reference, traced, harness, work):
    header = MAPS["HEADER"]
    writer = work / "parameter-writer"
    native_build = reference.parent
    run("cc", "-Wall", "-Wextra", "-Werror", "-I", source / "c/include",
        SCRIPTS / "brotli-context-header/parameter-writer.c", "-L", native_build,
        f"-Wl,-rpath,{native_build}", "-lbrotlienc", "-o", writer)
    output = {}
    for name, (wire, provenance, configured) in header["inputs"](reference, writer, harness, work).items():
        start, maps, counts, expected = native_header(wire, reference, traced)
        if configured is not None:
            check(tuple(expected["distance"]) == configured, "configured native distance parameters")
        file = work / "wire.br"
        file.write_bytes(wire)
        stop = expected["payload"]
        entries = sum(m["entries"] for m in maps)
        result = run("lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                     "--run", HERE / "Interop.lean", file, str(start), str(stop), str(entries),
                     str(sum(counts)), str(counts[-1] - 1))
        actual = json.loads(result.stdout)
        for key, value in expected.items():
            check(actual.get(key) == value, f"{name}: Lean header field {key}")
        alphabets = [group[0][0] for group in expected["groups"]]
        fields_hash = sha256(json.dumps(expected, separators=(",", ":"), sort_keys=True).encode()).hexdigest()
        output[name] = {"provenance": provenance, "sha256": sha256(wire).hexdigest(),
                        "header_sha256": fields_hash, "start": start, "payload": stop,
                        "counts": counts, "alphabets": alphabets, "distance": expected["distance"]}
        print(f"{name}: header [{start}, {stop}), counts {counts}, alphabets {alphabets}")
    check(any(all(x > 1 for x in row["counts"]) for row in output.values()), "multi-tree groups")
    check({row["distance"][0] for row in output.values()} == {0, 1, 2, 3}, "distance postfix coverage")
    check(any(row["alphabets"][2] == 520 for row in output.values()), "maximal distance alphabet")
    return output


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--brotli-source", type=Path)
    args = parser.parse_args()
    check((pa.__version__, version("thrift")) == ("26.0.1", "0.25.0"), "producer versions")
    harness = runpy.run_path(str(SCRIPTS / "parquet-brotli-raw/check.py"))
    check(harness["PIN"] == PIN, "libbrotli pin")
    with TemporaryDirectory(prefix="silmaril-brotli-compressed-header-") as temp:
        work = Path(temp)
        clean = work / "clean"
        clean.mkdir()
        source = args.brotli_source.resolve() if args.brotli_source else None
        reference = harness["build_reference"](source, clean)
        source = source or clean / "brotli"
        traced = MAPS["setup_trace"](source, work, HERE / "trace-reference.py")
        manifest = {"libbrotli_commit": PIN, "fixtures": collect(source, reference, traced, harness, work)}
        check(manifest == json.loads((HERE / "fixtures.json").read_text()), "wire and header fixture pins")
        print(f"Fixture manifest matched libbrotli {PIN}, PyArrow {pa.__version__}, Thrift {version('thrift')}")


if __name__ == "__main__":
    main()
