#!/usr/bin/env python3
"""Update generated-input pins and the Lean dependency marker, not upstream/ELF pins."""
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / 'corpus/cjson/semantic-inputs/linux-x86_64/predicates'
LITERALS = ['context.c', 'typed-ail.sexp', 'program.sexp', 'runtime.sexp']


def literal_digest():
    digest = hashlib.sha256()
    for name in LITERALS:
        data = (DATA / name).read_bytes()
        digest.update(len(data).to_bytes(8, 'little'))
        digest.update(data)
    return digest.hexdigest()


def main():
    manifest = DATA / 'manifest.json'
    pins = json.loads(manifest.read_text())
    generated = set(LITERALS + ['projection.json'])
    for entry in pins['files']:
        path = ROOT / entry['path']
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        if path.parent == DATA and path.name in generated:
            entry['sha256'] = actual
        elif actual != entry['sha256']:
            raise SystemExit(f"refusing to change non-generated pin: {entry['path']}")
    source = ROOT / 'Silmaril/Elf/Corpus/CjsonTypePredicates/Source/Defs.lean'
    text, count = re.subn(r'(def externalInputSha256 : String := ")[0-9a-f]*(")',
                         lambda match: match[1] + literal_digest() + match[2], source.read_text())
    assert count == 1, 'missing Lean external-input dependency marker'
    source.write_text(text)
    manifest.write_text(json.dumps(pins, indent=2) + '\n')


if __name__ == '__main__':
    main()
