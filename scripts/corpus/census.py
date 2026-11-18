#!/usr/bin/env python3
"""Tool evidence for canonical and optimization/stripping ELFs. Run inside corpus/toolchain's pinned image.

No execution or Lean proof is implied. Each artifact is independently generated;
readelf/objdump failures stop generation rather than silently dropping coverage.
"""
import argparse
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

# Deliberately bounded exact-mnemonic evidence, not an exhaustive classifier.
FEATURE_MNEMONICS = {
    'x86_64': {'AES': 'aesenc aesenclast aesdec aesdeclast aesimc aeskeygenassist',
               'SHA': 'sha1msg1 sha1msg2 sha1nexte sha1rnds4 sha256msg1 sha256msg2 sha256rnds2',
               'BMI2': 'bzhi mulx pdep pext rorx sarx shlx shrx',
               'ADX': 'adcx adox', 'RDRAND': 'rdrand', 'RDSEED': 'rdseed'},
    'aarch64': {'AES': 'aese aesd aesmc aesimc',
                'SHA1': 'sha1c sha1p sha1m sha1h sha1su0 sha1su1',
                'SHA256': 'sha256h sha256h2 sha256su0 sha256su1',
                'CRC32': 'crc32b crc32h crc32w crc32x crc32cb crc32ch crc32cw crc32cx'},
}


def run(tool, *args):
    return subprocess.check_output([tool, *map(str, args)], text=True, env={**os.environ, 'LC_ALL': 'C'})


def disassembly(text, arch):
    sections = {}
    current = None
    for line in text.splitlines():
        m = re.match(r'Disassembly of section (.+):', line)
        if m:
            current = sections.setdefault(m[1], {'decoded_bytes': 0, 'undecoded_bytes': 0,
                                                'mnemonics': Counter(), 'syscall_sites': []})
            continue
        # -w keeps byte columns on one line; AArch64 prints one 32-bit word.
        width = 2 if arch == 'x86_64' else 8
        m = re.match(r'^\s*([0-9a-f]+):\s+((?:[0-9a-f]{' + str(width) + r'}\s+)+)\s*(\S+)(.*)$', line)
        if not m or current is None:
            continue
        raw = ''.join(m[2].split())
        mnemonic = m[3]
        size = len(raw) // 2
        invalid = mnemonic.startswith('.') or mnemonic in ('(bad)', 'undefined')
        current['undecoded_bytes' if invalid else 'decoded_bytes'] += size
        current['mnemonics'][mnemonic] += 1
        if mnemonic in ('syscall', 'sysenter', 'svc') or (mnemonic == 'int' and '$0x80' in m[4]):
            current['syscall_sites'].append({'address': int(m[1], 16), 'instruction': mnemonic + m[4],
                                            'number': None, 'number_status': 'not inferred'})
    return sections


def census(path, arch):
    prefix = '' if arch == 'x86_64' else 'aarch64-linux-gnu-'
    readelf, objdump = prefix + 'readelf', prefix + 'objdump'
    dynamic = run(readelf, '-dW', path)
    symbols = run(readelf, '-sW', path)
    programs = run(readelf, '-lW', path)
    section_text = run(readelf, '-SW', path)
    relocations = run(readelf, '-rW', path)
    decoded = disassembly(run(objdump, '-dw', path), arch)
    executable = []
    for line in section_text.splitlines():
        m = re.match(r'\s*\[\s*\d+\]\s+(\S+)\s+\S+\s+([0-9a-f]+)\s+[0-9a-f]+\s+([0-9a-f]+)\s+\S+\s+(\S+)', line)
        if m and 'X' in m[4]:
            evidence = decoded.get(m[1], {'decoded_bytes': 0, 'undecoded_bytes': 0, 'mnemonics': {}, 'syscall_sites': []})
            size = int(m[3], 16)
            accounted = evidence['decoded_bytes'] + evidence['undecoded_bytes']
            if accounted > size:
                raise ValueError(f'{path}: decoder byte count exceeds section {m[1]}')
            executable.append({'name': m[1], 'address': int(m[2], 16), 'size': size,
                               **evidence, 'unreported_bytes': size - accounted})
    imports = sorted(set(m[1] for m in re.finditer(r'^\s*\d+:\s+\S+\s+\S+\s+\S+\s+\S+\s+\S+\s+UND\s+(\S+)', symbols, re.M)))
    relocation_counts = Counter(re.findall(r'\bR_(?:X86_64|AARCH64)_\w+', relocations))
    mnemonics = Counter()
    for section in executable:
        mnemonics.update(section['mnemonics'])
    extensions = {feature: {name: mnemonics[name] for name in names.split() if mnemonics[name]}
                  for feature, names in FEATURE_MNEMONICS[arch].items()}
    tags = lambda tag: re.findall(r'\(' + tag + r'\).*?\[(.*?)\]', dynamic)
    feature_patterns = {'threads': r'^(pthread_|thrd_)', 'signals': r'^(sigaction|signal|sigprocmask|pthread_sigmask)(@|$)',
                        'futex': r'^futex(@|$)', 'vdso': r'(__vdso_|__kernel_)'}
    return {'schema_version': 1, 'path': str(path), 'sha256': hashlib.file_digest(path.open('rb'), 'sha256').hexdigest(),
            'arch': arch, 'evidence_kind': 'tool-derived static evidence; not a Lean proof',
            'analysis_image_id': os.environ.get('CORPUS_ANALYSIS_IMAGE_ID', 'not recorded'),
            'generator_sha256': hashlib.file_digest(Path(__file__).open('rb'), 'sha256').hexdigest(),
            'tools': {'readelf': run(readelf, '--version').splitlines()[0], 'objdump': run(objdump, '--version').splitlines()[0]},
            'dynamic': {'needed': tags('NEEDED'), 'soname': tags('SONAME'), 'rpath': tags('RPATH'), 'runpath': tags('RUNPATH'),
                        'interpreter': re.findall(r'Requesting program interpreter: (.*?)\]', programs),
                        'version_information': run(readelf, '-VW', path), 'imports': imports},
            'relocations': dict(sorted(relocation_counts.items())),
            'abi_evidence': {'tls_program_header': bool(re.search(r'^\s*TLS\s', programs, re.M)),
                             'ifunc_symbols': sorted(set(re.findall(r'^.*\bIFUNC\b.*$', symbols, re.M))),
                             'import_matches': {k: [s for s in imports if re.search(p, s)] for k, p in feature_patterns.items()}},
            'executable_sections': executable,
            'extension_evidence': {'method': 'exact mnemonic matches in linear disassembly; bounded allowlist',
                                   'classifier': FEATURE_MNEMONICS[arch], 'matches': extensions},
            'elf_notes': run(readelf, '-nW', path),
            'dynamic_observations': {'status': 'not measured', 'syscalls': None},
            'limits': ['Linear objdump decoding can interpret embedded data as instructions; not control-flow reachability.',
                       'Mnemonic counts are decoder evidence, not complete ISA-extension classification or semantic support.',
                       'Imports do not demonstrate runtime use; static linking, indirect calls and inline syscalls can hide dependencies.',
                       'Absent import matches or syscall sites do not establish absence of a feature or dependency.',
                       'Syscall numbers, indirect targets, signal behavior, vDSO use and runtime effects remain unknown.']}


def report_relative_path(artifact_path):
    """Keep canonical report URLs stable; variants retain their full build identity."""
    path = Path(artifact_path)
    if path.is_relative_to('corpus/elf'):
        relative = path.relative_to('corpus/elf')
    elif path.is_relative_to('corpus/variants'):
        relative = Path('variants') / path.relative_to('corpus/variants')
    else:
        raise ValueError(f'{path}: outside corpus artifact roots')
    return relative.parent / (relative.name + '.json')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root', type=Path, default=Path('.'))
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--variants-only', action='store_true', help='analyze completed variants without regenerating canonical reports')
    a = p.parse_args()
    os.chdir(a.root)
    count = 0
    receipts = [] if a.variants_only else sorted(Path('corpus/elf').glob('*/*/receipt.json'))
    receipts += sorted(Path('corpus/variants').glob('*/*/*/*/*/*/receipt.json'))
    for receipt_path in receipts:
        receipt = json.loads(receipt_path.read_text())
        for obj in receipt['outputs']:
            path = Path(obj['path'])
            if hashlib.file_digest(path.open('rb'), 'sha256').hexdigest() != obj['sha256']:
                raise ValueError(f'{path}: receipt hash mismatch before analysis')
            report = census(path, receipt['arch'])
            if report['sha256'] != obj['sha256']:
                raise ValueError(f'{path}: receipt hash mismatch')
            report['identity'] = {'project': receipt['package'], 'version': receipt['version'],
                                  'receipt': str(receipt_path), 'receipt_sha256': hashlib.file_digest(receipt_path.open('rb'), 'sha256').hexdigest(),
                                  'inputs': receipt['inputs'], 'image': receipt['image'],
                                  'compiler': receipt['compiler'], 'cflags': receipt['cflags'],
                                  'configure_args': receipt['configure_args'], 'stripping': 'unstripped' if obj['has_symtab'] else 'no-symtab'}
            if 'variant' in receipt:
                report['identity']['variant'] = receipt['variant']
                report['identity']['stripping'] = receipt['variant']['stripping']
            out = a.output / report_relative_path(path)
            out.parent.mkdir(parents=True, exist_ok=True)
            out.write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
            count += 1
    print(f'census: {count} artifacts')


if __name__ == '__main__':
    main()
