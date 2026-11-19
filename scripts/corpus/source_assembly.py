#!/usr/bin/env python3
"""Hash-checked source assembly inventory; lexical evidence, not reachability.

Only explicit volatile asm syntax in included C-family files is classified here.
Standalone assembler inputs stay separate. Preprocessor activity is unknown.
"""
import argparse
import hashlib
import json
from pathlib import Path
import platform
import re


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def volatile_asm_sites(text):
    # Preserve line numbers while removing comments and quoted strings, so a
    # comment or a compiler-command string cannot fabricate a source asm site.
    comments_strings = r'//[^\n]*|/\*[\s\S]*?\*/|"(?:\\[\s\S]|[^"\\])*"|\'(?:\\[\s\S]|[^\'\\])*\''
    code = re.sub(comments_strings, lambda m: re.sub(r'[^\n]', ' ', m[0]), text)
    pattern = r'\b(?:__asm__|__asm|asm)\s+(?:__volatile__|__volatile|volatile)\s*\('
    lines = text.splitlines()
    return [{'line': code.count('\n', 0, match.start()) + 1,
             'source_line': lines[code.count('\n', 0, match.start())].strip()}
            for match in re.finditer(pattern, code)]


def inventory(root, build_path):
    build = json.loads((root / build_path).read_text())
    standalone, inline = [], []
    for source in build['included_source_files']:
        path = root / source['path']
        if sha(path) != source['sha256']:
            raise ValueError(f'{path}: source changed since build')
        if path.suffix in ['.S', '.s']:
            standalone.append({**source, 'origin': 'build-generated' if 'generated' in path.parts else 'upstream archive input'})
        elif path.name.endswith(('.c', '.h', '.cc', '.hh', '.hpp', '.c.inc', '.cc.inc', '.h.inc')):
            sites = volatile_asm_sites(path.read_text(errors='replace'))
            if sites:
                inline.append({**source, 'explicit_volatile_asm_syntax': sites})
    return {'schema_version': 1, 'build': str(build_path), 'build_sha256': sha(root / build_path),
            'tool_sha256': sha(Path(__file__)), 'python': platform.python_version(),
            'evidence': 'lexical syntax in exact included source bytes; separate from compiler-emitted assembly',
            'standalone_assembly_inputs': standalone, 'c_family_volatile_asm_sources': inline,
            'limits': ['Source inclusion does not establish that an asm site survives target preprocessing or executes.',
                       'Only explicit volatile asm syntax is classified; nonvolatile forms, macros, builtins and C++ raw strings need separate analysis.',
                       'Standalone .S/.s is never classified as C inline assembly.',
                       'No source semantics, Lean proof, function correspondence or ISA support is inferred.']}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root', type=Path, required=True)
    p.add_argument('--build', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    result = inventory(a.root, a.build)
    with a.output.open('x') as out:
        out.write(json.dumps(result, indent=2, sort_keys=True) + '\n')


if __name__ == '__main__':
    main()
