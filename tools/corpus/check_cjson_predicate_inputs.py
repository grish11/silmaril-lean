#!/usr/bin/env python3
"""Check recorded public cJSON source inputs; does not rebuild an ELF or prove semantics."""
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / "corpus/cjson/semantic-inputs/linux-x86_64/predicates"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    digest = hashlib.sha256()
    for name in ['context.c', 'typed-ail.sexp', 'program.sexp', 'runtime.sexp']:
        data = (DATA / name).read_bytes()
        digest.update(len(data).to_bytes(8, 'little'))
        digest.update(data)
    source = (ROOT / 'Silmaril/Elf/Corpus/CjsonTypePredicates/Source/Defs.lean').read_text()
    marker = re.search(r'def externalInputSha256 : String := "([0-9a-f]{64})"', source)
    assert marker and marker[1] == digest.hexdigest(), 'external literals changed without Lean dependency marker'
    manifest = json.loads((DATA / "manifest.json").read_text())
    for entry in manifest["files"]:
        path = ROOT / entry["path"]
        if sha(path) != entry["sha256"]:
            raise SystemExit(f"changed recorded input: {entry['path']}")
    projection = json.loads((DATA / "projection.json").read_text())
    tu = (DATA / "translation-unit.i").read_bytes()
    closure = (DATA / "context.c").read_bytes()
    assert hashlib.sha256(tu).hexdigest() == projection["tu_sha256"]
    assert all(0 <= a < b <= len(tu) for a, b in projection["spans"])
    assert b"\n".join(tu[a:b] for a, b in projection["spans"]) + b"\n" == closure
    receipt = json.loads((DATA / "preprocess-receipt.json").read_text())
    for entry in receipt["input_files"]:
        if not entry["path"].startswith("/"):
            assert sha(ROOT / entry["path"]) == entry["sha256"]
    print(f"PASS {len(manifest['files'])} public input pins and {len(projection['spans'])} exact TU spans; no full-TU/semantic claim")


if __name__ == "__main__":
    main()
