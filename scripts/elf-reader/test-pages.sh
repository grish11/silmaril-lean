#!/usr/bin/env bash
# The ELF pages are derived from the checked theorems, and nothing else (tools/elf-pages):
#  1. generate them into a temporary directory and verify them (`elf-pages --verify`);
#  2. move a theorem's window, re-associate a theorem with another part, or mark a byte range
#     as decoded in the JSON: --verify must reject each edit.
set -euo pipefail
cd "$(dirname "$0")/../.."
out=$(mktemp -d); trap 'rm -rf "$out"' EXIT
pages() { lake env .lake/build/bin/elf-pages "$@"; }
pages "$out" >/dev/null
pages --verify "$out" >/dev/null
f="$out/elf/f/gnu-sha256sum.json"
cp "$f" "$out/orig.json"
tamper() {  # tamper NAME PYTHON-EXPRESSION-ON-d
  python3 -I -c "import json,sys; d=json.load(open(sys.argv[1])); $2; json.dump(d, open(sys.argv[1],'w'))" "$f"
  if pages --verify "$out" >/dev/null 2>&1; then echo "test-pages: --verify accepted a tampered page ($1)" >&2; exit 1; fi
  cp "$out/orig.json" "$f"
}
tamper "window moved" "t=next(t for t in d['theorems'] if t['part']=='phdr/3'); t['windows'][0][0]+=56"
tamper "theorem re-associated" "t=next(t for t in d['theorems'] if t['part']=='phdr/3'); t['part']='phdr/4'"
tamper "coverage widened" "d['coverage'][0][2]='decoded' if d['coverage'][0][2]!='decoded' else 'raw'"
tamper "axioms hidden" "d['theorems'][0]['axioms']=[]"
pages --verify "$out" >/dev/null
echo "test-pages: ok"
