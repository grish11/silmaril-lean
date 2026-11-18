# corpus/depfiles.py -- repository-authored helper (run with python3 -I inside the image).
# Usage: depfiles.py ROOT [DEPFILE|DIR ...]
# Prints, sorted and unique, the absolute paths of existing files under ROOT that the compiler
# depfiles name (targets excluded). With no DEPFILE/DIR arguments, scans ROOT for *.d, *.Po, *.Plo.
# Relative names are resolved against ROOT first, then against the depfile's directory and its
# parents (recursive makes).
import os, sys
root = os.path.realpath(sys.argv[1])
args = sys.argv[2:] or [root]
deps = []
for a in args:
    if os.path.isdir(a):
        for d, _, fs in os.walk(a):
            deps += [os.path.join(d, f) for f in fs if f.endswith(('.d', '.Po', '.Plo'))]
    elif os.path.isfile(a):
        deps.append(a)
out = set()
for df in deps:
    try:
        text = open(df, encoding='utf-8', errors='surrogateescape').read()
    except OSError:
        continue
    text = text.replace('\\\n', ' ')
    for line in text.splitlines():
        if ':' not in line or line.startswith('#'):
            continue
        _, _, rhs = line.partition(': ')
        if not rhs and line.rstrip().endswith(':'):
            rhs = line.rstrip()[:-1]   # "-MP" phony line: "hdr.h:"
        for name in rhs.replace('\\ ', '\0').split():
            name = name.replace('\0', ' ')
            if os.path.isabs(name):
                cands = [name]
            else:
                cands = [os.path.join(root, name)]
                d = os.path.dirname(os.path.realpath(df))
                while d.startswith(root):
                    cands.append(os.path.join(d, name))
                    d = os.path.dirname(d)
            for c in cands:
                c = os.path.normpath(c)
                if os.path.isfile(c):
                    if os.path.realpath(c).startswith(root + os.sep):
                        out.add(os.path.normpath(c))
                    break
print('\n'.join(sorted(out)))
