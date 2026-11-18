# corpus/receipt.py -- repository-authored helper (python3 -I, inside the toolchain image).
# Usage: receipt.py PKGDIR ARCH OBJDIR REPRODUCIBLE(true|false) IMAGE_TAG IMAGE_ID BASE_DIGEST
# Reads OBJDIR/.build-info (written by build.sh) and OBJDIR/.tests.jsonl (written by test.sh),
# measures every object in OBJDIR, and writes OBJDIR/receipt.json and OBJDIR/SHA256SUMS.
import hashlib, json, os, re, subprocess, sys, tomllib
pkgdir, arch, objdir, repro, tag, image_id, base = sys.argv[1:8]
pkg = tomllib.load(open(os.path.join(pkgdir, 'package.toml'), 'rb'))
info = {}
for line in open(os.path.join(objdir, '.build-info'), encoding='utf-8'):
    k, _, v = line.rstrip('\n').partition('\t')
    info.setdefault(k, []).append(v)
one = lambda k, d='': info.get(k, [d])[-1]
tp = '' if arch == 'x86_64' else 'aarch64-linux-gnu-'
def first_line(cmd):
    return subprocess.run(cmd, capture_output=True, text=True).stdout.splitlines()[0]
def readelf(*a):
    return subprocess.run([tp + 'readelf', *a], capture_output=True, text=True, check=True).stdout
outputs = []
names = sorted(f for f in os.listdir(objdir) if not f.startswith('.') and f not in ('receipt.json', 'SHA256SUMS'))
for name in names:
    p = os.path.join(objdir, name)
    data = open(p, 'rb').read()
    machine = re.search(r'Machine:\s+(.*)', readelf('-hW', p)).group(1).strip()
    syms, cur = readelf('-sW', p), None
    count = 0
    for l in syms.splitlines():
        m = re.match(r"Symbol table '([^']+)'", l)
        if m:
            cur = m.group(1); continue
        f = l.split()
        if cur == '.symtab' and len(f) >= 8 and f[0].endswith(':') and f[3] == 'FUNC' and f[6] != 'UND':
            size = int(f[2], 16) if f[2].startswith('0x') else int(f[2])
            if size: count += 1
    sections = readelf('-SW', p)
    outputs.append({'object': name, 'path': f'corpus/elf/{pkg["name"]}/{arch}/{name}',
                    'size': len(data), 'sha256': hashlib.sha256(data).hexdigest(),
                    'elf_machine': machine, 'func_symbols': count,
                    'has_symtab': '.symtab' in sections, 'has_debug_info': '.debug_' in sections})
tests = []
tp_path = os.path.join(objdir, '.tests.jsonl')
if os.path.exists(tp_path):
    tests = [json.loads(l) for l in open(tp_path, encoding='utf-8') if l.strip()]
receipt = {
    'package': pkg['name'], 'version': pkg['version'], 'arch': arch,
    'image': {'tag': tag, 'id': image_id, 'base': base},
    'compiler': first_line([tp + 'gcc', '--version']),
    'binutils': first_line([tp + 'ld', '--version']),
    'cflags': one('cflags'), 'ldflags': one('ldflags'), 'configure_args': one('configure_args'),
    'build_commands': info.get('command', []),
    'SOURCE_DATE_EPOCH': int(os.environ['SOURCE_DATE_EPOCH']),
    'build_dir': one('build_dir'),
    'inputs': [{'url': v.split()[0], 'sha256': v.split()[1]} for v in info.get('input', [])],
    'outputs': outputs,
    'reproducible': repro == 'true',
    'reproducibility_check': 'two clean builds (fresh containers, fresh /build) compared by sha256',
    'tests': tests,
}
for k in ('notes',):
    if k in info: receipt[k] = info[k]
json.dump(receipt, open(os.path.join(objdir, 'receipt.json'), 'w'), indent=2)
open(os.path.join(objdir, 'receipt.json'), 'a').write('\n')
with open(os.path.join(objdir, 'SHA256SUMS'), 'w') as f:
    for o in outputs:
        f.write(f"{o['sha256']}  {o['object']}\n")
