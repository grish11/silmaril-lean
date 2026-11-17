#!/usr/bin/env python3
"""Index only completed canonical/variant artifacts, checking bytes and receipts.

No pending manifest entries are emitted. Content IDs and build identities are
separate: identical bytes can be outcomes of distinct builds.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import tomllib

ROOT = Path(__file__).resolve().parents[2]


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def sha(path):
    with path.open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


def inventory(root):
    artifacts = []
    formal_path = root / 'corpus/measurements/formal-functions/checks.json'
    formal = json.loads(formal_path.read_text())['statements'] if formal_path.exists() else []
    if len({s['declaration'] for s in formal}) != len(formal):
        raise ValueError('duplicate concrete formal statement')
    for statement in formal:
        if statement['kind'] not in ['functional_equivalence', 'contextual_c_to_elf'] or statement['status'] != 'stated-unproved':
            raise ValueError('unsupported formal statement status')
        run = json.loads((root / statement['run_receipt']).read_text())
        if run['exit_code'] != 0 or statement['root'] not in run['command']:
            raise ValueError('formal statement check receipt mismatch')
        for path, expected in {**statement['artifact_sha256'], **statement['module_sha256']}.items():
            if sha(root / path) != expected:
                raise ValueError(f'{path}: changed since formal statement check')
    check_path = root / 'corpus/measurements/variant-lean/checks.json'
    checked_variants = {c['path']: c for c in json.loads(check_path.read_text())['artifacts']} if check_path.exists() else {}
    receipts = sorted((root / 'corpus/elf').glob('*/*/receipt.json'))
    receipts += sorted((root / 'corpus/variants').glob('*/*/*/*/*/*/receipt.json'))
    for path in receipts:
        receipt = json.loads(path.read_text())
        package = tomllib.loads((root / 'corpus' / receipt['package'] / 'package.toml').read_text())
        variant = receipt.get('variant', {'optimization': 'O2', 'stripping': 'unstripped',
                                           'configuration': 'no-asm' if receipt['package'] == 'openssl' else 'default',
                                           'target': receipt['arch'] + '-linux-gnu'})
        source = sorted(receipt['inputs'], key=lambda x: (x['url'], x['sha256']))
        source_id = digest(source)
        build = {'source_id': source_id, 'configuration': variant['configuration'],
                 'target': variant['target'], 'compiler': receipt['compiler'],
                 'binutils': receipt['binutils'], 'cflags': receipt['cflags'],
                 'ldflags': receipt['ldflags'], 'configure_args': receipt['configure_args'],
                 'image': receipt['image'], 'SOURCE_DATE_EPOCH': receipt['SOURCE_DATE_EPOCH']}
        for obj in receipt['outputs']:
            artifact = root / obj['path']
            if sha(artifact) != obj['sha256'] or artifact.stat().st_size != obj['size']:
                raise ValueError(f'{artifact}: receipt identity mismatch')
            lean_status = 'not generated or checked'
            if path.is_relative_to(root / 'corpus/elf'):
                context_path = root / 'corpus' / receipt['package'] / 'tv' / receipt['arch'] / (obj['object'] + '.tsv')
                context = json.loads(context_path.read_text().splitlines()[0].removeprefix('# '))
                thms = root / (context['decomposition_module'].removesuffix('.Decomp').replace('.', '/') + '/Thms.lean')
                if re.search(r'^theorem parses\b', thms.read_text(), re.M):
                    lean_status = 'canonical: whole-file parse and structural decomposition'
                else:
                    lean_status = 'canonical: checked layout and structural decomposition; whole-file parse unavailable'
            elif obj['path'] in checked_variants:
                check = checked_variants[obj['path']]
                run = json.loads((root / check['run_receipt']).read_text())
                if check['sha256'] != obj['sha256'] or run['exit_code'] != 0 or check['root'] not in run['command']:
                    raise ValueError(f'{artifact}: Lean check receipt mismatch')
                prefix = check['root'].removesuffix('.Decomp').replace('.', '/')
                required = {prefix + '/' + name + '.lean' for name in ['Bytes', 'Defs', 'Thms', 'Functions', 'Decomp']}
                if not required.issubset(check['module_sha256']):
                    raise ValueError(f'{artifact}: incomplete Lean module hash receipt')
                for source_path, expected_sha in check['module_sha256'].items():
                    if sha(root / source_path) != expected_sha:
                        raise ValueError(f'{source_path}: changed since measured Lean check')
                lean_status = 'variant: whole-file parse and structural decomposition; measured check receipt'
            artifacts.append({'project': receipt['package'], 'version': receipt['version'],
                'version_components': re.split(r'[.+-]', receipt['version']),
                'source_id': source_id, 'source_inputs': source, 'build_id': digest(build),
                'build': build, 'optimization': variant['optimization'], 'stripping': variant['stripping'],
                'path': obj['path'], 'sha256': obj['sha256'], 'size': obj['size'],
                'receipt': str(path.relative_to(root)), 'receipt_sha256': sha(path),
                'license': package['license'], 'license_files': package.get('license_files', []),
                'defined_nonzero_function_symbol_entries': obj['func_symbols'],
                'has_symtab': obj['has_symtab'], 'reproducible': receipt['reproducible'],
                'runtime_tests': receipt['tests'],
                'lean_status': lean_status,
                'formal_statements': [{k: s[k] for k in ['kind', 'status', 'declaration', 'root']} for s in formal if obj['path'] in s['artifact_sha256']],
                'contextual_c_to_elf_statements': sum(s['kind'] == 'contextual_c_to_elf' and obj['path'] in s['artifact_sha256'] for s in formal),
                'functional_equivalence_statements': sum(s['kind'] == 'functional_equivalence' and obj['path'] in s['artifact_sha256'] for s in formal)})
    return {'schema_version': 1,
            'hierarchy': ['project', 'version_components', 'source_id', 'build.configuration',
                          'build.target', 'build.compiler', 'build.cflags', 'stripping', 'sha256'],
            'formal_statement_counts': {kind: sum(s['kind'] == kind for s in formal) for kind in ['contextual_c_to_elf', 'functional_equivalence']},
            'artifact_rows': len(artifacts), 'unique_content_hashes': len({a['sha256'] for a in artifacts}),
            'limits': ['Only completed hash-checked outputs are indexed; no planned builds count as artifacts.',
                       'Symbol entries include aliases and are not unique semantic functions.',
                       'Build identity and source metadata are not C semantics or a translation-validation statement.'],
            'artifacts': artifacts}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--check', action='store_true')
    a = p.parse_args()
    text = json.dumps(inventory(ROOT), indent=2, sort_keys=True) + '\n'
    if a.check:
        if a.output.read_text() != text:
            raise SystemExit('matrix differs: regenerate from actual completed receipts')
    else:
        a.output.write_text(text)
    print('matrix: ' + str(len(json.loads(text)['artifacts'])) + ' delivered artifact rows')


if __name__ == '__main__':
    main()
