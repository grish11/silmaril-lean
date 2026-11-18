"""Bounded public registry → read-only corpus bindings. No Lean/compiler execution.

Unlike fixture manifests this never imports proof evidence or marks refinement
proved. ELF function excerpts are static files, never added to the project DB.
"""
import hashlib
import json
from pathlib import Path
import re
import sqlite3
import struct

ROOT = Path(__file__).resolve().parents[2]
REGISTRY = 'corpus/measurements/formal-functions/checks.json'
MAX_TEXT = 2 * 1024 * 1024
STRING = r'"(?:\\.|[^"\\])*"'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def public_file(root, name):
    path = (root / name).resolve()
    if Path(name).is_absolute() or '..' in Path(name).parts or not path.is_relative_to(root.resolve()) or not name.startswith(('corpus/', 'Silmaril/', 'benchmarks/', 'tools/', 'tests/')):
        raise ValueError('non-public corpus input: ' + name)
    return path


def literal(data, spec):
    text = data.decode()
    pattern = (r'def ' + re.escape(spec['name']) + r'\s*:\s*String\s*:=\s*(' + STRING + ')'
               if 'name' in spec else re.escape(spec['marker']) + r'\s*(' + STRING + ')')
    matches = list(re.finditer(pattern, text))
    if len(matches) != 1:
        raise ValueError('expected one exact literal: ' + str(spec))
    m = matches[0]
    return json.loads(m[1]).encode(), {'module': spec['module_literal'],
        'literal_offset': len(text[:m.start(1)].encode()), 'literal_length': len(m[1].encode()),
        'module_sha256': sha(data), 'extraction': 'exact recorded Lean string literal; not a new elaboration/exporter run'}


def elf_function(data, name, wanted=None):
    """Read actual ELF64LE STT_FUNC + executable PT_LOAD bytes; reject ambiguity."""
    if data[:6] != b'\x7fELF\x02\x01':
        raise ValueError('expected ELF64 little endian')
    phoff, shoff = struct.unpack_from('<QQ', data, 32)
    phsize, phnum, shsize, shnum = struct.unpack_from('<HHHH', data, 54)
    def section(i):
        return struct.unpack_from('<IIQQQQIIQQ', data, shoff + i * shsize)
    found = set()
    for i in range(shnum):
        s = section(i)
        if s[1] not in (2, 11):
            continue
        names_section = section(s[6])
        strings = data[names_section[4]:names_section[4] + names_section[5]]
        if s[9] != 24:
            raise ValueError('unexpected ELF symbol entry')
        for at in range(s[4], s[4] + s[5], s[9]):
            n, info, _, _, addr, size = struct.unpack_from('<IBBHQQ', data, at)
            if info & 15 == 2 and strings[n:strings.index(0, n)].decode() == name and size:
                if wanted is None or addr == wanted:
                    found.add((addr, size))
    if len(found) != 1:
        raise ValueError('ambiguous/missing ELF function: ' + name)
    addr, size = found.pop()
    if not 0 < size <= 65536:
        raise ValueError('unbounded function excerpt')
    for i in range(phnum):
        kind, flags, off, va, _, filesz, _, _ = struct.unpack_from('<IIQQQQQQ', data, phoff + i * phsize)
        if kind == 1 and flags & 1 and va <= addr and addr + size <= va + filesz:
            offset = off + addr - va
            code = data[offset:offset + size]
            if len(code) != size:
                raise ValueError('truncated function')
            return {'address': addr, 'size': size, 'file_offset': offset,
                    'bytes_hex': code.hex(' '), 'code_sha256': sha(code),
                    'identity_check': 'ELF symbol + executable PT_LOAD bytes checked by Python; kernel CodeAt lives in the linked Lean modules'}
    raise ValueError('function outside executable file-backed segment')


def export(project, output, root=ROOT):
    registry_data = public_file(root, REGISTRY).read_bytes()
    statements = [s for s in json.loads(registry_data)['statements'] if s['kind'] == 'contextual_c_to_elf']
    manifests = []
    for path in sorted((root / 'corpus/compiler-bindings').glob('*.json')):
        data = path.read_bytes()
        manifests.append({**json.loads(data), '_manifest': {'path': path.relative_to(root).as_posix(), 'sha256': sha(data)}})
    groups = {m['registry_root']: m for m in manifests}
    if len(groups) != len(manifests) or set(groups) != {s['root'] for s in statements}:
        raise ValueError('corpus manifests must cover exactly the registered contextual roots')
    db = sqlite3.connect(project.resolve().as_uri() + '?mode=ro', uri=True)
    try:
        db.row_factory = sqlite3.Row
        revision = db.execute("SELECT value FROM corpus_meta WHERE key='revision'").fetchone()[0]
        if not re.fullmatch('[0-9a-f]{40}', revision):
            raise ValueError('missing immutable public source revision')
        output.mkdir(parents=True, exist_ok=True)
        (output / 'blobs').mkdir(exist_ok=True)
        def blob(data, identity):
            if len(data) > MAX_TEXT:
                raise ValueError('corpus text exceeds bounded export')
            digest = sha(data)
            (output / 'blobs' / (digest + '.txt')).write_bytes(data)
            return {**identity, 'sha256': digest, 'size': len(data), 'static_path': 'api/corpus/blobs/' + digest + '.txt'}
        listing = []
        checked = set()
        for statement in statements:
            if statement['status'] != 'stated-unproved':
                raise ValueError('new status needs explicit corpus viewer review')
            pins = {**statement['module_sha256'], **statement['artifact_sha256']}
            for name, digest in pins.items():
                if (name, digest) not in checked:
                    if sha(public_file(root, name).read_bytes()) != digest:
                        raise ValueError('stale registered corpus evidence: ' + name)
                    checked.add((name, digest))
            m = groups[statement['root']]
            if m['schema'] != 'silmaril.corpus-view.v1':
                raise ValueError('unsupported corpus manifest')
            def read(name):
                if name not in pins:
                    raise ValueError('input not pinned by this statement: ' + name)
                return public_file(root, name).read_bytes()
            def resource(spec):
                if 'path' in spec:
                    return blob(read(spec['path']), {'path': spec['path']})
                data, identity = literal(read(spec['module_literal']), spec)
                return blob(data, identity)
            source = resource(m['source'])
            core = resource(m['core'])
            projection = m['projection']
            tu = read(projection['tu'])
            if 'path' in projection:
                receipt = json.loads(read(projection['path']))
                if sha(tu) != receipt.get('sha256', receipt.get('tu_sha256')):
                    raise ValueError('source TU identity mismatch')
                spans = []
                for item in receipt['spans']:
                    if isinstance(item, dict):
                        a, n = item['offset'], item['length']
                        if sha(tu[a:a+n]) != item['sha256']:
                            raise ValueError('source span identity mismatch')
                    else:
                        a, end = item
                        n = end - a
                    spans.append([a, n])
                joined = b'\n'.join(tu[a:a+n] for a, n in spans) + b'\n'
            else:
                spans = projection['spans']
                joined = b''.join(tu[a:a+n] for a, n in spans)
            if sha(joined) != source['sha256']:
                raise ValueError('exact source closure/span mismatch: ' + statement['function_symbol'])
            source['projection'] = {'tu': projection['tu'], 'tu_sha256': sha(tu),
                                    'spans': [{'offset': a, 'length': n, 'sha256': sha(tu[a:a+n])} for a, n in spans]}
            artifacts = []
            for name, digest in statement['artifact_sha256'].items():
                row = db.execute('SELECT id,sha256 FROM corpus_artifacts WHERE path=?', (name,)).fetchone()
                if row is None or row['sha256'] != digest:
                    raise ValueError('catalog artifact mismatch: ' + name)
                function = elf_function(read(name), statement['function_symbol'], statement.get('function_address'))
                count = db.execute('SELECT count(*) FROM corpus_functions WHERE artifact=? AND symbol=? AND address=? AND size=?',
                    (row['id'], statement['function_symbol'], function['address'], function['size'])).fetchone()[0]
                if not count:
                    raise ValueError('catalog function mismatch')
                artifact = {'id': row['id'], 'path': name, 'sha256': digest, **function}
                # Optional actual callees are excerpts from this SAME pinned ELF,
                # never a contract, a generated body or an additional proof.
                callees = m.get('callees', [])
                if not isinstance(callees, list) or len(callees) > 8:
                    raise ValueError('unbounded corpus callee list')
                seen_callees = set()
                for callee in callees:
                    if set(callee) != {'symbol', 'address', 'size'} or not isinstance(callee['symbol'], str) or not isinstance(callee['address'], int) or not isinstance(callee['size'], int):
                        raise ValueError('invalid corpus callee identity')
                    if callee['symbol'] in seen_callees or callee['symbol'] == statement['function_symbol']:
                        raise ValueError('duplicate corpus callee')
                    seen_callees.add(callee['symbol'])
                    actual = elf_function(read(name), callee['symbol'], callee['address'])
                    if actual['size'] != callee['size']:
                        raise ValueError('callee ELF size mismatch')
                    count = db.execute('SELECT count(*) FROM corpus_functions WHERE artifact=? AND symbol=? AND address=? AND size=?',
                        (row['id'], callee['symbol'], actual['address'], actual['size'])).fetchone()[0]
                    if not count:
                        raise ValueError('catalog callee mismatch')
                    artifact.setdefault('callees', []).append({'function_symbol': callee['symbol'], **actual})
                artifacts.append(artifact)
            modules = [blob(read(name), {'path': name}) for name in m['context_modules']]
            payload = {'schema': m['schema'], 'declaration': statement['declaration'], 'root': statement['root'],
                'status': 'UNPROVED', 'registry_status': statement['status'], 'function_symbol': statement['function_symbol'],
                'registry': {'path': REGISTRY, 'sha256': sha(registry_data)}, 'manifest': m['_manifest'], 'revision': revision,
                'source': source, 'core': core, 'context_modules': modules, 'artifacts': artifacts,
                'limits': m['limits'], 'run_receipt': statement['run_receipt'],
                'mapping': 'Function-level contextual obligation only; no source-line/instruction segment mapping.',
                'proof_evidence': None, 'exporter_run': None, 'interactive_compilation': False}
            if 'runtime' in m:
                payload['runtime'] = resource(m['runtime'])
            key = sha(statement['declaration'].encode())
            (output / (key + '.json')).write_text(json.dumps(payload, indent=2) + '\n')
            listing.append({k: payload[k] for k in ('declaration', 'function_symbol', 'root', 'status')})
            listing[-1]['static_path'] = 'api/corpus/' + key + '.json'
    finally:
        db.close()
    (output / 'index.json').write_text(json.dumps(listing, indent=2) + '\n')
    return listing
