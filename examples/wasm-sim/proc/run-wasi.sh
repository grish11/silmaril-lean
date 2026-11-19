#!/bin/sh
# Run an x86-64 ELF on the all-Wasm stack under plain `wasmtime run`:
#   mem (memory model) + sys (syscalls over WASI) + core (simulator) + extrun (foreign calls)
#   + ffi (foreign library: ffi-none or libc) + loader (ELF loader, launcher); io = shared
#   WASI memory; ext/nd = stubs (only x86-mini imports the simulator ABI's callback-style ext.call).
# usage: [WSIM_SIM=mini|g|m|path.wasm] [WSIM_EXT=ffi-none|libc] [WSIM_SCHED=rr|rand] run-wasi.sh PROG ARGS...
# PROG is relative to the current directory (preopened as the WASI root).
set -eu
D="$(cd "$(dirname "$0")" && pwd)/build"
case "${WSIM_SIM:-mini}" in
  mini) SIM="$D/x86-mini.wasm";; g|m) SIM="$D/x86-$WSIM_SIM.wasm";; *) SIM="$WSIM_SIM";;
esac
# WSIM_SCHED=rr|rand: threads (clone) and a scheduler (sched.wasm + policy-$WSIM_SCHED.wasm)
CORE="--preload core=$SIM"
if [ -n "${WSIM_SCHED:-}" ]; then
  CORE="--preload core0=$SIM --preload sched=$D/policy-$WSIM_SCHED.wasm --preload core=$D/sched.wasm"
fi
exec wasmtime run --dir . \
  --preload io="$D/io.wasm" --preload mem="$D/mem.wasm" --preload sys="$D/sys.wasm" --preload nd="$D/stubs.wasm" \
  --preload ext="$D/stubs.wasm" --preload ffi="$D/${WSIM_EXT:-ffi-none}.wasm" \
  $CORE --preload sim="$D/extrun.wasm" \
  "$D/loader.wasm" "$@"
