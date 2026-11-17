# corpus/funcmap.py -- repository-authored helper (python3 -I, inside the toolchain image).
# Usage: funcmap.py ARCH PINNED TWIN OUT.json
# Maps every function symbol of the pinned ELF object to its C source, through the DWARF of its
# debug twin (the same build with -g instead of -g0; twin.sh). First it checks that the twin's code
# is the pinned object's: .text byte-identical, and the same defined function symbols (name,
# value, size). Then, per function symbol of .text:
#   bound      a DWARF subprogram of a compile unit starts at the symbol's value: its C name, CU
#              (translation unit), declaration line, external/static, and addr2line's file:line
#   clone      a compiler-generated clone (name.part.N, .constprop.N, .isra.N, .cold, ...): its
#              origin's C name, no source function of its own
#   no-dwarf   no compile unit describes it (start-up/runtime objects compiled without -g, assembly)
# and, apart from symbols: C functions of the units with no code of their own (inlined into
# callers or eliminated), so the matrix also covers C functions with no ELF symbol.
# Every entry is tool-derived (binutils readelf/addr2line on the twin), never a proof.
import json, re, subprocess, sys
arch, pinned, twin, out = sys.argv[1:5]
tp = '' if arch == 'x86_64' else 'aarch64-linux-gnu-'
def run(*a): return subprocess.run(a, check=True, capture_output=True, text=True, errors='replace').stdout
def text_bytes(f):
    for l in run('readelf', '-SW', f).splitlines():
        m = re.match(r'\s*\[\s*\d+\]\s+\.text\s+\S+\s+([0-9a-f]+)\s+([0-9a-f]+)\s+([0-9a-f]+)', l)
        if m:
            addr, off, size = (int(x, 16) for x in m.groups())
            with open(f, 'rb') as h:
                h.seek(off); return addr, h.read(size)
    return None, b''
def funcs(f):
    r = {}
    for l in run('readelf', '-sW', f).splitlines():
        p = l.split()
        if len(p) >= 8 and p[3] in ('FUNC', 'IFUNC') and p[6] != 'UND':
            r.setdefault((p[7].split('@')[0], int(p[1], 16), int(p[2], 0)), p)
    return r
pa, pt = text_bytes(pinned); ta, tt = text_bytes(twin)
fp, ft = funcs(pinned), funcs(twin)
identical = pa == ta and pt == tt and set(fp) == set(ft)
symbols_identical = set(fp) == set(ft)
text_diff = sum(1 for x, y in zip(pt, tt) if x != y) + abs(len(pt) - len(tt))
# DWARF: every DIE (offset, depth, tag, attributes); subprograms of depth 1 are the C functions
dies, cus, cu, stack = {}, [], None, []
for l in subprocess.Popen(['readelf', '--debug-dump=info', twin], stdout=subprocess.PIPE, text=True, errors='replace').stdout:
    m = re.match(r'\s*<(\d+)><([0-9a-f]+)>: Abbrev Number: \d+ \((DW_TAG_\w+)\)', l)
    if m:
        depth, off, tag = int(m[1]), int(m[2], 16), m[3]
        d = {'tag': tag, 'kids': [], 'off': off}
        dies[off] = d
        del stack[depth:]
        if stack: stack[-1]['kids'].append(d)
        stack.append(d)
        if depth == 0:
            cu = {'name': None, 'subs': [], 'die': d}; cus.append(cu)
        elif depth == 1 and tag == 'DW_TAG_subprogram' and cu is not None:
            cu['subs'].append(d)
        continue
    m = re.match(r'\s*<[0-9a-f]+>\s+(DW_AT_\w+)\s*:\s*(.*)', l)
    if not m or not stack: continue
    at, v = m[1][6:], m[2].strip()
    v = re.sub(r'^\(indirect (line )?string, offset: 0x[0-9a-f]+\):\s*', '', v)
    d = stack[-1]
    if at == 'low_pc': d['low_pc'] = int(v, 16)
    elif at == 'decl_line': d['line'] = int(v, 0)
    elif at in ('type', 'call_origin', 'abstract_origin', 'specification'):
        r = re.match(r'<0x([0-9a-f]+)>', v); d[at] = int(r[1], 16) if r else v
    else: d[at] = v
    if len(stack) == 1 and at == 'name' and cu is not None and cu['name'] is None: cu['name'] = v
def kind(t, seen=0):
    """C type class of a DIE offset: void, int, float, ptr, struct, other."""
    d = dies.get(t) if isinstance(t, int) else None
    if d is None: return 'void'
    tg = d['tag']
    if tg in ('DW_TAG_typedef', 'DW_TAG_const_type', 'DW_TAG_volatile_type', 'DW_TAG_restrict_type', 'DW_TAG_atomic_type') and seen < 20:
        return kind(d.get('type'), seen + 1)
    if tg == 'DW_TAG_base_type':
        return 'float' if 'float' in d.get('encoding', '') or 'complex' in d.get('encoding', '') else 'int'
    if tg == 'DW_TAG_enumeration_type': return 'int'
    if tg in ('DW_TAG_pointer_type', 'DW_TAG_reference_type'): return 'ptr'
    if tg in ('DW_TAG_structure_type', 'DW_TAG_union_type', 'DW_TAG_array_type'): return 'struct'
    return 'other'
def origin(d):
    o = d
    for _ in range(4):
        n = o.get('abstract_origin') or o.get('specification')
        if isinstance(n, int) and n in dies: o = dies[n]
        else: break
    return o
def sig(d):
    o = origin(d)
    ps = [kind(k.get('type')) for k in o['kids'] if k['tag'] == 'DW_TAG_formal_parameter']
    var = any(k['tag'] == 'DW_TAG_unspecified_parameters' for k in o['kids'])
    calls, ind = set(), 0
    def walk(x):
        nonlocal ind
        for k in x['kids']:
            if k['tag'] in ('DW_TAG_call_site', 'DW_TAG_GNU_call_site'):
                co = k.get('call_origin') or k.get('abstract_origin')
                if isinstance(co, int) and co in dies: calls.add(origin(dies[co]).get('name', '?'))
                else: ind += 1
            walk(k)
    walk(d)
    return {'params': ps, 'result': kind(o.get('type')), 'variadic': var, 'callees': sorted(calls), 'indirect_calls': ind,
            'prototyped': o.get('prototyped', '') != ''}
for c in cus:
    for x in c['subs']:
        o = origin(x)
        if 'name' not in x and 'name' in o: x['name'] = o['name']
        if 'external' not in x and 'external' in o: x['external'] = o['external']
        if 'line' not in x and 'line' in o: x['line'] = o['line']
by_pc = {}
for c in cus:
    for s in c['subs']:
        if 'low_pc' in s: by_pc.setdefault(s['low_pc'], (c['name'], s))
rows, text_lo, text_hi = [], ta or 0, (ta or 0) + len(tt)
addrs = []
for (name, val, size), p in sorted(fp.items(), key=lambda x: x[0][1]):
    if not (text_lo <= val < text_hi) or size == 0: continue
    r = {'symbol': name, 'value': val, 'size': size, 'bind': p[4]}
    hit = by_pc.get(val)
    base = re.split(r'\.(part|constprop|isra|cold|lto_priv|localalias|clone)\b', name)[0]
    if hit and 'name' in hit[1] and hit[1]['name'] == base:
        cuname, s = hit
        r.update(status='bound', c_name=s['name'], tu=cuname, decl_line=s.get('line'), external='external' in s, **sig(s))
        addrs.append(val)
    elif base != name:
        r.update(status='clone', c_name=base, tu=hit[0] if hit else None)
        addrs.append(val)
    else:
        # code in DW_AT_ranges (hot/cold split): bind by name when exactly one unit defines it
        cand = [(c['name'], x) for c in cus for x in c['subs'] if x.get('name') == name and ('ranges' in x or 'low_pc' in x)]
        if len(cand) > 1:
            # several units define `name`: keep the one whose file the address's line entry names
            f = subprocess.run([tp + 'addr2line', '-e', twin, hex(val)], capture_output=True, text=True).stdout.split(':')[0]
            f = re.sub(r'^(\./)+', '', f)
            cand = [c for c in cand if c[0] and f.endswith(re.sub(r'^(\./)+', '', c[0]).split('/', 1)[-1])] or cand
        if len(cand) == 1:
            r.update(status='bound', via='ranges+name', c_name=name, tu=cand[0][0], decl_line=cand[0][1].get('line'), external='external' in cand[0][1], **sig(cand[0][1]))
            addrs.append(val)
        else:
            # no subprogram DIE: the line table may still place the address in a source file
            a = subprocess.run([tp + 'addr2line', '-e', twin, hex(val)], capture_output=True, text=True).stdout.strip()
            if not cand and re.match(r'.+\.[ch]:\d+', a):
                r.update(status='bound-line', c_name=name, tu=re.sub(r'^(\./)+', '', a.split(':')[0]), first_line=a)
            else:
                r.update(status='no-dwarf' if not cand else 'ambiguous', candidates=[c for c, _ in cand])
    rows.append(r)
loc = {}
if addrs:
    a2l = subprocess.run([tp + 'addr2line', '-e', twin], input='\n'.join(hex(a) for a in addrs), capture_output=True, text=True).stdout.split('\n')
    loc = dict(zip(addrs, a2l))
for r in rows:
    if r['value'] in loc: r['first_line'] = loc[r['value']]
emitted = {(c['name'], s.get('name')) for c in cus for s in c['subs'] if 'low_pc' in s or 'ranges' in s}
nocode = sorted({(c['name'], s['name'], s.get('line')) for c in cus for s in c['subs']
                 if 'name' in s and 'low_pc' not in s and 'ranges' not in s and 'declaration' not in s and 'abstract_origin' not in s and 'specification' not in s and (c['name'], s['name']) not in emitted})
counts = {}
for r in rows: counts[r['status']] = counts.get(r['status'], 0) + 1
json.dump({'arch': arch, 'object': pinned.rsplit('/', 1)[-1], 'twin_code_identical': identical,
           'twin_symbols_identical': symbols_identical, 'twin_text_bytes_differing': text_diff,
           'text': {'address': pa, 'size': len(pt)}, 'counts': counts,
           'c_functions_without_code': len(nocode), 'compile_units': len(cus), 'functions': rows,
           'without_code': [{'tu': t, 'c_name': n, 'decl_line': ln} for t, n, ln in nocode]},
          open(out, 'w'), separators=(',', ':'), sort_keys=True)
print(f"{pinned}: identical={identical} symbols={symbols_identical} text_diff={text_diff} {counts} without_code={len(nocode)}")
