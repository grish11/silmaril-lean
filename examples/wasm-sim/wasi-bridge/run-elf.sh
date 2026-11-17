#!/bin/sh
# Run an x86-64 ELF on the simulator stack with the syscall → WASI adapter `sys2wasi` as the
# syscall layer (the proc stack of ../proc/run-wasi.sh with sys.wasm replaced).
# usage: [WSIM_SIM=mini|g|m] run-elf.sh PROG ARGS...   (PROG relative to the current directory)
set -eu
D="$(cd "$(dirname "$0")" && pwd)"; P="$D/../proc/build"
[ -f "$D/build/sys2wasi.wasm" ] || { mkdir -p "$D/build"; wat2wasm "$D/wat/sys2wasi.wat" -o "$D/build/sys2wasi.wasm"; }
case "${WSIM_SIM:-g}" in mini|g|m) SIM="$P/x86-${WSIM_SIM:-g}.wasm";; *) SIM="$WSIM_SIM";; esac
exec wasmtime run --dir . \
  --preload io="$P/io.wasm" --preload mem="$P/mem.wasm" --preload sys="$D/build/sys2wasi.wasm" \
  --preload nd="$P/stubs.wasm" --preload ext="$P/stubs.wasm" --preload ffi="$P/ffi-none.wasm" \
  --preload core="$SIM" --preload sim="$P/extrun.wasm" "$P/loader.wasm" "$@"
