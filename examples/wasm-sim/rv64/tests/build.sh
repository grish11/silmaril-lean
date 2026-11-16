#!/bin/sh
# Assemble the RV64 test programs (no C extension: the simulators implement RV64IM).
# usage: build.sh <outdir>
set -e
here=$(dirname "$0")
out=${1:-/tmp/wsim-rv}
mkdir -p "$out"
LLD=${LLD:-$(command -v ld.lld || ls ~/.elan/toolchains/*/bin/ld.lld | head -1)}
CC="clang --target=riscv64-linux-gnu -march=rv64im -mabi=lp64 -mno-relax -nostdlib -static --ld-path=$LLD"
for f in hello arith memops; do $CC -o "$out/$f" "$here/$f.S"; done
$CC -DHOT_N=1000 -o "$out/loops" "$here/loops.S"
$CC -DHOT_N=20000000 -o "$out/bench" "$here/loops.S"
for f in "$here"/*.c; do
  [ -e "$f" ] || continue
  b=$(basename "$f" .c)
  $CC -O2 -ffreestanding -fno-builtin -fno-pic -o "$out/$b" "$here/crt.S" "$f"
done
