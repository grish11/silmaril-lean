# local/extract-rfc6234.py -- repository-authored (ours). Why: RFC 6234 publishes its reference C code
# only inside the RFC text (section 8); this script cuts the files out of the verbatim RFC text
# (upstream/rfc6234/rfc6234.txt) so they can be compiled. It changes nothing in the code itself; it only
# removes the RFC page furniture (the "Eastlake & Hansen ... [Page N]" footer, the form feed and the
# "RFC 6234 ... May 2011" header, plus the blank padding lines around them) and the prose between files.
# Usage: python3 -I extract-rfc6234.py RFC6234.TXT OUTDIR
import os, re, sys
src, outdir = sys.argv[1], sys.argv[2]
lines = open(src, encoding='ascii').read().split('\n')
# 1. drop page breaks: blank lines + footer + "\f" header + blank lines
clean, i = [], 0
footer = re.compile(r'^Eastlake & Hansen\s+Informational\s+\[Page \d+\]$')
while i < len(lines):
    if footer.match(lines[i]):
        while clean and clean[-1] == '':
            clean.pop()
        i += 1
        while i < len(lines) and lines[i] == '\f':
            i += 1
        if i < len(lines) and lines[i].lstrip('\f').startswith('RFC 6234 '):
            i += 1
        while i < len(lines) and lines[i] == '':
            i += 1
        continue
    clean.append(lines[i]); i += 1
# 2. each file starts with its banner line and runs to the next "8.x" / "9." section heading
banner = re.compile(r'^/\*{4,} ([A-Za-z0-9_.-]+) \*{4,}/$')
heading = re.compile(r'^\d+(\.\d+)*\.  \S')
start = clean.index('8.  C Code for SHAs, HMAC, and HKDF')
end = clean.index('9.  Security Considerations')
files, cur = {}, None
for l in clean[start:end]:
    m = banner.match(l)
    if m:
        cur = m.group(1); files[cur] = []
    elif heading.match(l):
        cur = None
    if cur:
        files[cur].append(l)
# stdint-example.h has no banner line: take its section body
os.makedirs(outdir, exist_ok=True)
for name, body in files.items():
    while body and body[-1] == '':
        body.pop()
    with open(os.path.join(outdir, name), 'w', encoding='ascii') as f:
        f.write('\n'.join(body) + '\n')
    print(name, len(body))
