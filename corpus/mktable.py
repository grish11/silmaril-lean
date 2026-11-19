# corpus/mktable.py -- repository-authored helper (python3 -I, host side).
# Usage: mktable.py REPO -- rewrites the object table in corpus/README.md (between the
# "objects:begin" / "objects:end" markers) from corpus/elf/*/*/receipt.json and package.toml,
# and prints the byte totals of corpus and corpus/elf.
import json, os, sys, tomllib
repo = sys.argv[1]
src, art = os.path.join(repo, 'corpus'), os.path.join(repo, 'corpus/elf')
order = ['sqlite', 'cjson', 'jemalloc', 'mimalloc', 'darkhttpd', 'tcp-pingpong', 'refcrypto', 'coreutils', 'openssl']
rows = ['| package | version | arch | path | size | sha256 | FUNC syms | reproducible | tests | licence |',
        '|---|---|---|---|---:|---|---:|---|---|---|']
for pkg in order:
    toml = os.path.join(src, pkg, 'package.toml')
    if not os.path.exists(toml):
        continue
    lic = tomllib.load(open(toml, 'rb'))['license']
    for arch in ('x86_64', 'aarch64'):
        rp = os.path.join(art, pkg, arch, 'receipt.json')
        if not os.path.exists(rp):
            continue
        r = json.load(open(rp))
        npass = sum(t['result'].startswith('pass') for t in r['tests'])
        nfail = sum(t['result'].startswith('FAIL') for t in r['tests'])
        for o in r['outputs']:
            rows.append(f"| {pkg} | {r['version']} | {arch} | `{o['path']}` | {o['size']} | `{o['sha256']}` | {o['func_symbols']} | {'yes' if r['reproducible'] else 'NO'} | {npass} pass / {nfail} fail | {lic} |")
def total(d):
    return sum(os.path.getsize(os.path.join(p, f)) for p, _, fs in os.walk(d) for f in fs)
tot = f"Totals: corpus {total(src)} bytes; corpus/elf {total(art)} bytes."
readme = os.path.join(src, 'README.md')
text = open(readme).read()
b, e = '<!-- objects:begin -->', '<!-- objects:end -->'
i, j = text.index(b) + len(b), text.index(e)
open(readme, 'w').write(text[:i] + '\n' + '\n'.join(rows) + '\n\n' + tot + '\n' + text[j:])
print(tot)
