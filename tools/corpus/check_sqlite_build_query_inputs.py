#!/usr/bin/env python3
"""Check public actual-TU/build input identities; no artifact build or semantic proof."""
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / 'corpus/sqlite/semantic-inputs/3.54.1/default/x86_64/O2/build-queries'
LITERALS = ['context.c', 'typed-ail.sexp', 'program.sexp', 'runtime.sexp']


def digest():
    value = hashlib.sha256()
    for name in LITERALS:
        data = (DATA / name).read_bytes()
        value.update(len(data).to_bytes(8, 'little'))
        value.update(data)
    return value.hexdigest()


def main():
    pins = json.loads((DATA / 'manifest.json').read_text())
    for name, expected in pins['files'].items():
        assert hashlib.sha256((DATA / name).read_bytes()).hexdigest() == expected, name
    for name, expected in pins['immutable_files'].items():
        assert hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == expected, name
    source = (ROOT / 'Silmaril/Elf/Corpus/SqliteBuildQueries/Source/Defs.lean').read_text()
    marker = re.search(r'externalInputSha256 : String := "([0-9a-f]{64})"', source)
    assert marker and marker[1] == digest() == pins['external_input_sha256'], 'stale external literals'
    projection = json.loads((DATA / 'projection.json').read_text())
    tu = (DATA / 'translation-unit.i').read_bytes()
    assert hashlib.sha256(tu).hexdigest() == projection['sha256']
    preprocessing = json.loads((DATA / 'preprocessing.json').read_text())
    assert preprocessing['translation_unit_sha256'] == projection['sha256']
    canonical = json.loads((ROOT / preprocessing['canonical_receipt']).read_text())
    assert preprocessing['compiler'] == canonical['compiler']
    assert not preprocessing['historical_image_identity_established']
    assert not preprocessing['historical_header_identity_established']
    pieces = []
    for span in projection['spans']:
        offset, length = span['offset'], span['length']
        assert 0 <= offset < offset + length <= len(tu)
        piece = tu[offset:offset + length]
        assert hashlib.sha256(piece).hexdigest() == span['sha256']
        pieces.append(piece)
    assert b'\n'.join(pieces) + b'\n' == (DATA / 'context.c').read_bytes()
    print('PASS saved SQLite TU: 2 exact spans, public source/Core/runtime inputs and immutable source/ELF/receipt/runtime pins; preprocessing provenance limits retained')


if __name__ == '__main__':
    main()
