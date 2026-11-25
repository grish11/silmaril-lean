"""Describe the retained stages of one pinned SQLite reactor build."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys
from zipfile import ZipFile

WASM = Path(__file__).resolve().parents[1]
REPO = WASM.parents[1]
sys.path.insert(0, str(WASM))
from generate import export_index, read_manifest, read_u32, sections, vector

GETTER = "sqlite3_libversion_number"
SYMBOLS = (GETTER, "sqlite3GetVarint32", "sqlite3GetVarint", "sqlite3PutVarint", "putVarint64")
NATIVE = Path("corpus/sqlite/equivalence/native-compilers/manifest.json")
CODE = re.compile(r"\s*-\s+([0-9a-f]+)\s+([0-9a-f]+) CODE")
BODY = re.compile(r"\s*-\s+([0-9a-f]+)\s+([0-9a-f]+)\s+(\S.*):\(([^()]+)\)")


def sha(data):
    return hashlib.sha256(data).hexdigest()


def measure(path):
    with path.open("rb") as stream:
        return {"bytes": path.stat().st_size, "sha256": hashlib.file_digest(stream, "sha256").hexdigest()}


def function_frames(wasm):
    offset, payloads = 8, {}
    for kind, payload, framed in sections(wasm):
        payloads[kind] = (payload, offset, len(framed) - len(payload))
        offset += len(framed)
    imports = payloads[2][0]
    count, cursor = read_u32(imports, 0)
    for _ in range(count):
        for _ in range(2):  # module and field names
            size, start = read_u32(imports, cursor)
            cursor = start + size
        if imports[cursor] != 0:
            raise ValueError("pinned reactor must import only functions")
        _, cursor = read_u32(imports, cursor + 1)
    if cursor != len(imports):
        raise ValueError("unexpected Import section length")

    code, start, header = payloads[10]
    bodies = vector(code, sized=True)
    if len(bodies) != len(vector(payloads[3][0], sized=False)):
        raise ValueError("Function and Code counts differ")
    _, cursor = read_u32(code, 0)
    spans = []
    for body in bodies:
        spans.append((start + header + cursor, len(body)))
        cursor += len(body)
    version_slot = export_index(payloads[7][0], GETTER)
    return count, spans, start, header, len(code), version_slot


def map_frames(link_map, code_start, header, code_size):
    rows = []
    found = False
    for line in link_map.read_text().splitlines():
        if not found:
            if match := CODE.fullmatch(line):
                if tuple(int(n, 16) for n in match.groups()) != (code_start, code_size + header):
                    raise ValueError("link map CODE framing differs from the binary")
                found = True
            continue
        if line.endswith(" DATA"):
            break
        if match := BODY.fullmatch(line):
            offset, size, origin, symbol = match.groups()
            rows.append((int(offset, 16) + header, int(size, 16), origin, symbol))
    if not found or not rows:
        raise ValueError("no linker map Code frames")
    return rows


def defined_symbols(path):
    symbols = {name: [] for name in SYMBOLS}
    for line in path.read_text().splitlines():
        name, kind, *fields = line.split()
        if name in symbols and kind in ("t", "T"):
            symbols[name].append(fields)
    if any(len(entries) != 1 for entries in symbols.values()):
        raise ValueError(f"nonunique or missing selected symbol in {path.name}")
    return {name: entries[0] for name, entries in symbols.items()}


def source_join(archives, pin):
    native = json.loads((REPO / NATIVE).read_text())
    source = native["source"]
    archive = archives / Path(source["archive"]["url"]).name
    archive_pin = measure(archive)
    if archive_pin["sha256"] != source["archive"]["sha256"] or archive_pin["sha256"] != pin["source_archive_sha256"]:
        raise ValueError("native and reactor source archives differ")
    member = "/".join(Path(source["path"]).parts[-2:])
    with ZipFile(archive) as upstream:
        body = upstream.read(member)
    definition = source["definitions"][GETTER]
    start, length = definition["offset"], definition["length"]
    span = body[start:start + length]
    if sha(body) != source["sha256"] or sha(span) != definition["sha256"] or span.decode() != definition["text"]:
        raise ValueError("native source definition differs from the reactor input")
    pair, = (row for row in native["pairs"] if row["function_symbol"] == GETTER)
    return {
        "archive": {"name": archive.name, **archive_pin},
        "member": member, "sourceSha256": source["sha256"],
        "sharedDefinition": {
            "symbol": GETTER, "offset": start, "bytes": length, "sha256": sha(span),
            "nativeManifest": NATIVE.as_posix(), "nativeRecord": pair["id"],
        },
    }


def receipt(archives, stage):
    pin = read_manifest(WASM / "reactor.json")
    wasm = (stage / "sqlite3.wasm").read_bytes()
    if sha(wasm) != pin["artifact_sha256"]:
        raise ValueError("Wasm digest differs from the reactor pin")
    imports, spans, start, header, size, version_slot = function_frames(wasm)
    linked = map_frames(stage / "sqlite3.map", start, header, size)
    if [(offset, length) for offset, length, _, _ in linked] != spans:
        raise ValueError("link map Code entries differ from the binary")

    defined_symbols(stage / "sqlite3.bc.symbols")
    object_symbols = defined_symbols(stage / "sqlite3.o.symbols")
    selected = []
    for symbol in SYMBOLS:
        matches = [(imports + i, offset, length) for i, (offset, length, origin, name) in enumerate(linked)
                   if Path(origin).name == "sqlite3.o" and name == symbol]
        if len(matches) != 1:
            raise ValueError(f"nonunique or missing linked frame for {symbol}")
        index, offset, length = matches[0]
        if int(object_symbols[symbol][1], 16) != length:
            raise ValueError(f"relocatable symbol size differs for {symbol}")
        if symbol == GETTER and index != version_slot:
            raise ValueError("version export differs from its mapped slot")
        selected.append({"symbol": symbol, "wasmSlot": index, "codeOffset": offset, "codeBytes": length})

    sdk = archives / "wasi-sdk-30.0-x86_64-linux.tar.gz"
    return {
        "schema": "silmaril.sqlite-wasi-llvm-provenance.v1",
        "source": source_join(archives, pin),
        "sdk": {"name": sdk.name, **measure(sdk)},
        "commands": {"name": "clang-stages.txt", **measure(stage / "clang-stages.txt")},
        "stages": {name: measure(stage / name) for name in ("sqlite3.bc", "sqlite3.o", "sqlite3.wasm")},
        "inventory": {"functionImports": imports, "linkedCodeFrames": len(linked)},
        "symbols": sorted(selected, key=lambda row: row["wasmSlot"]),
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archives", type=Path)
    parser.add_argument("stage", type=Path)
    args = parser.parse_args()
    print(json.dumps(receipt(args.archives, args.stage), indent=2))
