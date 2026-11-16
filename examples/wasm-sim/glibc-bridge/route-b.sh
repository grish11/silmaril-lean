#!/bin/sh
# Route (b): glibc's own `puts` (pinned libc.so.6 = the host's, mapped and relocated in the
# simulated address space) on a Wasm simulator, its callees as imports; prints where it stops.
# Needs: cargo build --release --bin wsim-proc (tools/wasm-sim; CARGO_TARGET_DIR as you use).
#   1. puts in-sim                                     (strlen ifunc -> import)
#   2. + --fs: driver-level fs-relative mov/sub/cmp and lock cmpxchg (not in the simulators)
#   3. + malloc as an import, glibc's exit in-sim (for the stdio flush)
set -u
D="$(cd "$(dirname "$0")" && pwd)"; cd "$D/progs"
W=${WSIM_PROC:-${CARGO_TARGET_DIR:-$D/../../../.cargo-target}/release/wsim-proc}
L=${LIBC:-/usr/lib/x86_64-linux-gnu/libc.so.6}
for s in ${SIMS:-g m}; do
  echo "== sim $s: (1) puts in-sim"; $W glibc --sim $s --libc $L --in-sim puts hello-glibc 2>&1 | tail -1
  echo "== sim $s: (2) + --fs";      $W glibc --sim $s --libc $L --fs --in-sim puts hello-glibc 2>&1 | tail -1
  echo "== sim $s: (3) + malloc import, exit in-sim"
  $W glibc --sim $s --libc $L --fs --in-sim puts,exit --import malloc,__libc_malloc hello-glibc 2>&1
done
echo "== control: all imports bound to host functions"; $W glibc --sim g --libc $L hello-glibc 2>&1 | tail -2
