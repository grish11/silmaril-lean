#!/bin/sh
# Run a glibc-linked x86-64 ELF on the simulator stack, its glibc imports bound to the Wasm
# glibc-subset (build/glibc.wasm, WASI-backed) and its syscalls to sys2wasi:
#   loader-glibc (WASI _start) -> glibcrun -> core sim -> mem, sys2wasi;  ffi = glibc.wasm
# usage: [WSIM_SIM=mini|g|m] run-glibc.sh PROG ARGS...   (PROG relative to the current directory)
set -eu
D="$(cd "$(dirname "$0")" && pwd)"; B="$D/build"; P="$D/../proc/build"
case "${WSIM_SIM:-g}" in mini|g|m) SIM="$P/x86-${WSIM_SIM:-g}.wasm";; *) SIM="$WSIM_SIM";; esac
exec wasmtime run --dir . \
  --preload io="$P/io.wasm" --preload mem="$P/mem.wasm" --preload sys="$B/sys2wasi.wasm" \
  --preload nd="$P/stubs.wasm" --preload ext="$P/stubs.wasm" --preload ffi="$B/glibc.wasm" \
  --preload core="$SIM" --preload sim="$B/glibcrun.wasm" "$B/loader-glibc.wasm" "$@"
