#!/usr/bin/env python3
"""Check exact public source/TU/Core/build pins; no build or semantic proof."""
import hashlib
import json
from pathlib import Path
import re
ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / 'corpus/darkhttpd/semantic-inputs/1.17/default/x86_64/O0/needs-logencoding'
LITERALS = ['context.c', 'typed-ail.sexp', 'program.sexp', 'runtime.sexp']

def digest():
    h=hashlib.sha256()
    for name in LITERALS:
        b=(DATA/name).read_bytes();h.update(len(b).to_bytes(8,'little'));h.update(b)
    return h.hexdigest()

def main():
    m=json.loads((DATA/'manifest.json').read_text())
    for name,wanted in m['files'].items():
        assert hashlib.sha256((DATA/name).read_bytes()).hexdigest()==wanted,name
    for name,wanted in m['immutable_files'].items():
        assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==wanted,name
    source=(ROOT/'Silmaril/Elf/Corpus/DarkhttpdLogEncoding/Source/Defs.lean').read_text()
    marker=re.search(r'externalInputSha256 : String := "([0-9a-f]{64})"',source)
    assert marker and marker[1]==digest()==m['external_input_sha256'],'stale external literals'
    p=json.loads((DATA/'projection.json').read_text());tu=(DATA/'translation-unit.i').read_bytes()
    assert hashlib.sha256(tu).hexdigest()==p['tu_sha256']
    pieces=[]
    for span in p['spans']:
        b=tu[span['offset']:span['offset']+span['length']]
        assert hashlib.sha256(b).hexdigest()==span['sha256'];pieces.append(b)
    assert b'\n'.join(pieces)+b'\n'==(DATA/'context.c').read_bytes()
    original=(ROOT/p['source']).read_bytes();assert hashlib.sha256(original).hexdigest()==p['source_sha256']
    assert original[p['original_offset']:p['original_offset']+len(pieces[0])]==pieces[0]
    prep=json.loads((DATA/'preprocessing-context.json').read_text());r=json.loads((ROOT/prep['artifact_receipt']).read_text())
    assert prep['compiler']==r['compiler'] and prep['requested_cflags']==r['cflags']
    assert not prep['historical_image_identity_established'] and not prep['historical_header_identity_established']
    assert json.loads((DATA/'preprocessing.json').read_text())['exit_code']==0
    print('PASS actual darkhttpd source/TU span, computed-input identities and observed build pins; historical image/header/whole-TU adequacy remain unproved')
if __name__=='__main__':main()
