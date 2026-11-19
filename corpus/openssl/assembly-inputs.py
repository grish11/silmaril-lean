#!/usr/bin/env python3
"""Preserve available generators and standalone assembly after a real OpenSSL build.

Inclusion is not an invocation claim. Exact build-log generator commands are recorded
separately. C inline assembly and compiler builtins require their own analysis.
"""
import hashlib
import json
from pathlib import Path
import subprocess
import sys


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def version(command):
    return subprocess.check_output(command, text=True).splitlines()[0]


def inventory(root, pristine, arch):
    if arch not in ['x86_64', 'aarch64']:
        raise ValueError('unsupported OpenSSL assembly target')
    if not pristine.is_dir():
        raise ValueError('pristine OpenSSL archive tree is required for assembly provenance')
    prefix = '' if arch == 'x86_64' else 'aarch64-linux-gnu-'
    paths = sorted(p for p in root.rglob('*') if p.is_file() and
                   (p.suffix in ['.pl', '.pm', '.s', '.S'] or p.name == 'Configure' or
                    (p.suffix == '.conf' and p.is_relative_to(root / 'Configurations'))))
    generators, assembly = [], []
    for path in paths:
        rel = path.relative_to(root)
        item = {'path': str(rel), 'sha256': sha(path)}
        if path.suffix in ['.s', '.S']:
            original = pristine / rel
            item['origin'] = 'upstream' if original.is_file() and sha(original) == item['sha256'] else 'generated-or-modified'
            assembly.append(item)
        else:
            generators.append(item)
    commands = []
    for name in ['make-libs.log', 'make-apps.log']:
        for line in (root / name).read_text().splitlines():
            if '.pl' in line and 'perl' in line:
                commands.append({'log': name, 'command': line})
    result = {'configuration': 'asm', 'arch': arch,
              'tools': {'perl': version(['perl', '-e', 'print $^V']),
                        'compiler': version([prefix + 'gcc', '--version']),
                        'assembler': version([prefix + 'as', '--version'])},
              'available_generator_inputs': generators,
              'available_standalone_assembly': assembly, 'recorded_generator_commands': sorted(commands, key=lambda c: (c['log'], c['command'])),
              'limits': ['Available generator inputs are preserved conservatively, not all claimed invoked.',
                         'Available assembly is not all claimed assembled or linked; use exact build logs for that evidence.',
                         'Generated standalone assembly is not C inline assembly.',
                         'C inline assembly and compiler builtins are not classified by this inventory.',
                         'This is tool provenance, not Lean parsing or semantic validation.']}
    return paths, result


def main():
    root, pristine = map(lambda p: Path(p).resolve(), sys.argv[1:3])
    paths, result = inventory(root, pristine, sys.argv[3])
    output = root / 'assembly-provenance.json'
    output.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    for path in [*paths, output]:
        print(path)


if __name__ == '__main__':
    main()
