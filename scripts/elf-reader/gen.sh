#!/usr/bin/env bash
# Regenerate the per-part ELF reader modules (Silmaril/Elf/Staged/Pinned/*/{Bytes,Defs,Thms}.lean)
# from the pinned files of examples/elf/README.md.
#   scripts/elf-reader/gen.sh [--check]   with --check, fail if a module differs
set -euo pipefail
cd "$(dirname "$0")/../.."
check=${1:-}
examples/elf/pin.sh --check
lake build elf-staged >/dev/null
out=Silmaril/Elf/Staged/Pinned
dir=$out
if [ "$check" = --check ]; then dir=$(mktemp -d); trap 'rm -rf "$dir"' EXIT; fi
sha() { sha256sum "$1" | cut -d' ' -f1; }
# The unverified disassembly listing the explorer shows (examples/elf/disasm/SLUG.objdump): GNU
# objdump's output, with the objdump version on the first line. --check compares it only when the
# local objdump is the recorded version.
listing() {  # listing FILE SLUG
  local f=examples/elf/disasm/$2.objdump v
  if ! command -v objdump >/dev/null; then echo "gen.sh: no objdump; $f not regenerated or compared" >&2; return; fi
  v="# $(objdump --version | head -1)"
  if [ "$check" = --check ]; then
    if [ "$(head -1 "$f")" = "$v" ]; then
      cmp -s <(echo "$v"; echo "# objdump -d -w -z $1"; objdump -d -w -z "$1") "$f" || { echo "gen.sh: $f differs" >&2; exit 1; }
    else echo "gen.sh: $f was written by another objdump ($(head -1 "$f")); not compared" >&2; fi
  else
    mkdir -p examples/elf/disasm
    { echo "$v"; echo "# objdump -d -w -z $1"; objdump -d -w -z "$1"; } > "$f"
  fi
}
emit() {  # emit FILE NAME TITLE SLUG
  .lake/build/bin/elf-staged emit-reader "$1" "$2" "$(sha "$1")" "$3" "$dir" >/dev/null
  if [ "$check" = --check ]; then
    for m in Bytes Defs Thms; do
      cmp -s "$dir/$2/$m.lean" "$out/$2/$m.lean" || { echo "gen.sh: $out/$2/$m.lean differs" >&2; exit 1; }
    done
  fi
  listing "$1" "$4"
}
emit examples/dyn/pinned/hello-gcc HelloGcc '`hello` (gcc 13.3 -O2, glibc 2.39, `examples/dyn/hello/hello.c`)' hello-gcc
emit examples/elf/pinned/gnu-sha256sum Sha256sum 'GNU coreutils 9.4 (Ubuntu 9.4-3ubuntu6.3) `sha256sum`' gnu-sha256sum
echo "gen.sh: ok"
