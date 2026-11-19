#!/bin/sh
# Rebuild progs/hello.c with the system gcc (Ubuntu 24.04 gcc 13.3.0-6ubuntu2~24.04.1, binutils
# 2.42, libc6 2.39-0ubuntu8.9), compare with pinned/hello-glibc (SHA256SUMS), and print the file as
# the little-endian number of the Lean `Blob` in Silmaril/Sim/GlibcBridge/Elf/Defs.lean
# (`pin.sh --lean`).
# Receipt (2026-11-16): in ubuntu:24.04 at digest
# sha256:73b999393d07f2bf65a40373778a44dc9a6d54ad7718d29247d8ff9413c4d6a8 with gcc-13
# 13.3.0-6ubuntu2~24.04.1, binutils 2.42-4ubuntu2.10 and libc6-dev 2.39-0ubuntu8.12 the rebuild is
# byte-identical (sha256 367ebd46…20af).
set -eu
D="$(cd "$(dirname "$0")" && pwd)"; T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
gcc -O2 -no-pie -o "$T/hello-glibc" "$D/../progs/hello.c"
(cd "$T" && sha256sum -c "$D/SHA256SUMS") || { echo "pin.sh: rebuild differs" >&2; exit 1; }
if [ "${1:-}" = "--lean" ]; then
  echo "0x$(od -An -v -tx1 "$D/hello-glibc" | tr -s ' \n' '\n\n' | grep . | tac | tr -d '\n' | sed 's/^0*//'), $(wc -c < "$D/hello-glibc")"
fi
