#!/usr/bin/env python3
"""Check actual SQLite global-pointer source/TU/Core/ELF inputs; no builds or proof."""
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import struct
ROOT=Path(__file__).resolve().parents[2]
REL=Path('corpus/sqlite/semantic-inputs/3.54.1/default/x86_64/O2/global-version')
LITERALS=['context.c','typed-ail.sexp','program.sexp','runtime.sexp']
def digest(data): return hashlib.sha256(data).hexdigest()
def check(root=ROOT):
    data=root/REL;manifest=json.loads((data/'manifest.json').read_text())
    for name,expected in manifest['files'].items():assert digest((data/name).read_bytes())==expected,name
    for name,expected in manifest['immutable_files'].items():assert digest((root/name).read_bytes())==expected,name
    literals=digest(b''.join((data/name).read_bytes() for name in LITERALS))
    source=(root/'Silmaril/Elf/Corpus/SqliteGlobalVersion/Source/Defs.lean').read_text()
    marker=re.search(r'externalInputSha256 : String := "([0-9a-f]{64})"',source)
    assert marker and marker[1]==literals==manifest['external_input_sha256'],'stale literal marker'
    projection=json.loads((data/'projection.json').read_text())
    pieces=[]
    for path,key,spans in [('tu','tu_sha256','spans'),('source','source_sha256','original_spans')]:
        raw=(root/projection[path]).read_bytes();assert digest(raw)==projection[key],path+' identity'
        for span in projection[spans]:
            start,length=span['offset'],span['length'];assert 0<=start<start+length<=len(raw),'span range'
            piece=raw[start:start+length];assert digest(piece)==span['sha256'],path+' span'
            if path=='tu':pieces.append(piece)
    assert b'\n'.join(pieces)+b'\n'==(data/'context.c').read_bytes(),'projected source closure'
    prep=json.loads((root/manifest['preprocessing']).read_text())
    assert prep['translation_unit_sha256']==projection['tu_sha256'],'preprocessing TU identity'
    assert not prep['historical_image_identity_established'] and not prep['historical_header_identity_established']
    spec=importlib.util.spec_from_file_location('sqlite_global_corpus',root/'tools/compiler-explorer/corpus.py')
    c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
    raw=(root/manifest['elf']).read_bytes();f=c.elf_function(raw,'sqlite3_libversion',0x13810)
    assert f['bytes_hex']=='48 8b 05 b1 b7 0f 00 c3' and f['size']==8,'actual function bytes'
    code=bytes.fromhex(f['bytes_hex']);assert f['address']+7+int.from_bytes(code[3:7],'little',signed=True)==0x10efc8,'GOT displacement'
    phoff=struct.unpack_from('<Q',raw,32)[0];phsize,n=struct.unpack_from('<HH',raw,54)
    def mapped(address,size):
        for j in range(n):
            typ,flags,off,va,_,filesz,_,_=struct.unpack_from('<IIQQQQQQ',raw,phoff+j*phsize)
            if typ==1 and flags&4 and va<=address and address+size<=va+filesz:
                return raw[off+address-va:off+address-va+size]
        raise AssertionError('unmapped global data')
    assert mapped(0xed572,7)==b'3.54.1\0','actual global bytes'
    offset,info,addend=struct.unpack_from('<QQq',raw,53296)
    assert (offset,info>>32,info&0xffffffff,addend)==(0x10efc8,233,6,0),'actual GLOB_DAT relocation'
    print('PASS actual SQLite global-pointer source/TU/Core, executable bytes, global data and GOT relocation pins; post-loader restriction and whole-TU limits retained; UNPROVED')
if __name__=='__main__':check()
