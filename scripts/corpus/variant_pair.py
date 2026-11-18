#!/usr/bin/env python3
"""Record tool-derived mappings for an explicitly stripped ELF pair, inside the image."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys


def executable_sections(path, readelf):
    data = path.read_bytes()
    text = subprocess.check_output([readelf, '-SW', str(path)], text=True)
    result = {}
    for line in text.splitlines():
        m = re.match(r'\s*\[\s*\d+\]\s+(\S+)\s+\S+\s+([0-9a-f]+)\s+([0-9a-f]+)\s+([0-9a-f]+)\s+\S+\s+(\S+)', line)
        if m and 'X' in m[5]:
            offset, size = int(m[3], 16), int(m[4], 16)
            section = data[offset:offset + size]
            if len(section) != size:
                raise ValueError('section outside file')
            result[m[1]] = {'address': int(m[2], 16), 'size': size,
                            'sha256': hashlib.sha256(section).hexdigest()}
    return result


def main():
    arch, original, stripped, output = sys.argv[1:]
    original, stripped = Path(original), Path(stripped)
    tool = ('' if arch == 'x86_64' else 'aarch64-linux-gnu-') + 'readelf'
    before = executable_sections(original, tool)
    after = executable_sections(stripped, tool)
    if not before or before != after:
        raise ValueError('stripping changed executable section names, addresses, sizes or bytes')
    symbols = subprocess.check_output([tool, '-sW', str(original)], text=True)
    functions, table = [], None
    for line in symbols.splitlines():
        m = re.match(r"Symbol table '([^']+)'", line)
        if m:
            table = m[1]
        fields = line.split()
        if table == '.symtab' and len(fields) >= 8 and fields[0].endswith(':') and fields[3] in ('FUNC', 'IFUNC') and fields[6] != 'UND':
            size = int(fields[2], 16) if fields[2].startswith('0x') else int(fields[2])
            if size:
                functions.append({'name': fields[7], 'value': int(fields[1], 16), 'size': size,
                                  'section_index': fields[6], 'type': fields[3], 'binding': fields[4]})
    report = {'schema_version': 1, 'original_sha256': hashlib.sha256(original.read_bytes()).hexdigest(),
              'stripped_sha256': hashlib.sha256(stripped.read_bytes()).hexdigest(),
              'readelf': subprocess.check_output([tool, '--version'], text=True).splitlines()[0],
              'strip': subprocess.check_output([('' if arch == 'x86_64' else 'aarch64-linux-gnu-') + 'strip', '--version'], text=True).splitlines()[0],
              'evidence': 'paired artifacts: all executable sections have equal names, addresses, sizes and bytes',
              'executable_sections': before, 'unstripped_function_symbols': functions,
              'limits': 'Tool-derived address mapping from this exact pair; not recovered symbols in arbitrary stripped files, source binding, a Lean decomposition or functional equivalence proof.'}
    Path(output).write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')


if __name__ == '__main__':
    main()
