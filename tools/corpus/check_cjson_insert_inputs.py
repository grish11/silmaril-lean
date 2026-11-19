#!/usr/bin/env python3
"""Pin the actual saved-TU caller/helper, public Core and existing ELF; no semantic proof."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / 'corpus/cjson/semantic-inputs/linux-x86_64/insert-item-in-array'
LITERALS = ['context.c', 'typed-ail.sexp', 'program.sexp', 'runtime.sexp']


def check(root=ROOT):
    data = root / DATA.relative_to(ROOT)
    manifest = json.loads((data / 'manifest.json').read_text())
    digest = lambda content: hashlib.sha256(content).hexdigest()
    for name, expected in manifest['files'].items():
        assert digest((data / name).read_bytes()) == expected, name
    for name, expected in manifest['immutable_files'].items():
        assert digest((root / name).read_bytes()) == expected, name
    literals = digest(b''.join((data / name).read_bytes() for name in LITERALS))
    source = (root / 'Silmaril/Elf/Corpus/CjsonInsert/Source/Defs.lean').read_text()
    marker = re.search(r'externalInputSha256 : String := "([0-9a-f]{64})"', source)
    assert marker and marker[1] == literals == manifest['external_input_sha256'], 'stale literal marker'
    projection = json.loads((data / 'projection.json').read_text())
    tu = (root / projection['tu']).read_bytes()
    assert digest(tu) == projection['tu_sha256'], 'TU identity'
    pieces = []
    for span in projection['spans']:
        piece = tu[span['offset']:span['offset'] + span['length']]
        assert digest(piece) == span['sha256'], 'TU span'
        pieces.append(piece)
    assert b''.join(pieces) == (data / 'context.c').read_bytes(), 'projected source closure'
    original = (root / projection['source']).read_bytes()
    assert digest(original) == projection['source_sha256'], 'original source identity'
    print('PASS actual cJSON insertion/four-definition source/TU/Core/ELF pins; bounded actual caller/helper context remains UNPROVED')


if __name__ == '__main__':
    check()
