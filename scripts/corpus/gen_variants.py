#!/usr/bin/env python3
"""Generate staged readers/decompositions for explicit, hash-checked variant artifacts.

Generation does not establish that the emitted Lean modules elaborate. Build their
Decomp roots with --wfail and retain measured check receipts separately.
"""
import argparse
import os
from pathlib import Path
import subprocess
import tempfile
from gen import camel
from matrix import ROOT, inventory

GENERATOR = 'scripts/corpus/gen_variants.py'


def module_parts(artifact):
    path = Path(artifact['path'])
    if not path.is_relative_to('corpus/variants'):
        raise ValueError(f'{path}: expected a delivered variant')
    parts = ['Silmaril', 'Elf', 'Staged', 'CorpusVariants',
             *[camel(part) for part in path.relative_to('corpus/variants').parts]]
    # Project and executable often share a name (darkhttpd, sqlite, ...).
    # Keep generated namespaces unambiguous under Lean's duplicate-namespace linter.
    while parts[-1] in parts[:-1]:
        parts[-1] += 'Binary'
    return parts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--artifact', action='append', required=True,
                        help='exact repository-relative ELF path from the completed inventory')
    parser.add_argument('--max-table-entries', type=int, default=2000,
                        help='tables above this threshold use bounded checked windows')
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    if args.max_table_entries < 1:
        parser.error('--max-table-entries must be positive')
    artifacts = {a['path']: a for a in inventory(ROOT)['artifacts']}
    selected = []
    for path in dict.fromkeys(args.artifact):
        if path not in artifacts:
            parser.error(f'{path}: not a completed artifact')
        artifact = artifacts[path]
        selected.append((artifact, module_parts(artifact)))
    with tempfile.TemporaryDirectory(prefix='corpus-variant-gen-') as tmp:
        for artifact, parts in selected:
            namespace = '.'.join(parts)
            base = Path(*parts)
            definitions = ROOT / base / 'Defs.lean'
            if definitions.exists() and f'def path : String := \"{artifact["path"]}\"' not in definitions.read_text():
                raise FileExistsError(f'{definitions}: module-name collision with another artifact')
            result = subprocess.run([
                str(ROOT / '.lake/build/bin/elf-staged'), 'emit-reader', artifact['path'],
                '/'.join(parts[4:]), artifact['sha256'],
                f"{artifact['project']} {artifact['version']} {artifact['build']['target']} "
                f"{artifact['optimization']} {artifact['stripping']} `{artifact['path']}`",
                str(Path(tmp) / Path(*parts[:4])), '--namespace', namespace,
                '--include-path', os.path.relpath(ROOT / artifact['path'], ROOT / base),
                '--generator', GENERATOR, '--max-table-entries', str(args.max_table_entries)],
                cwd=ROOT, capture_output=True, text=True)
            if result.returncode:
                raise RuntimeError(result.stdout + result.stderr)
            generated = Path(tmp) / base
            for file in sorted(generated.rglob('*.lean')):
                destination = ROOT / file.relative_to(tmp)
                text = file.read_text()
                if args.check:
                    if not destination.exists() or destination.read_text() != text:
                        raise SystemExit(f'{destination}: generated reader differs')
                else:
                    if destination.exists() and GENERATOR not in destination.read_text():
                        raise FileExistsError(f'{destination}: preserve non-generator-owned file')
                    destination.parent.mkdir(parents=True, exist_ok=True)
                    destination.write_text(text)
            expected = {file.relative_to(generated) for file in generated.rglob('*.lean')}
            existing = {file.relative_to(ROOT / base) for file in (ROOT / base).rglob('*.lean')}
            if existing != expected:
                raise SystemExit(f'{base}: unexpected existing modules; review stale generated files')
            action = 'regeneration matches' if args.check else 'generated, not yet checked'
            print(f'{namespace}.Decomp: {action}', flush=True)


if __name__ == '__main__':
    main()
