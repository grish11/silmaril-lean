#!/bin/sh
# WASI → syscall → WASI round trip: link a WASI p1 program APP.wat with wasi2sys (its WASI
# imports become x86-64 syscalls) and sys2wasi (the syscalls become WASI again), wasm-merge'd
# into one module (build/rt-NAME.wasm). The program's imports are renamed to module `wasi2sys`
# and sys2wasi's process memory to `wasi2sys` (the WASI program's memory), so that only sys2wasi
# calls the real WASI host.  usage: roundtrip.sh APP.wat
set -eu
D="$(cd "$(dirname "$0")" && pwd)"; B="$D/build"; mkdir -p "$B"
n=$(basename "$1" .wat)
sed -e 's/"wasi_snapshot_preview1"/"wasi2sys"/g' -e 's/(export "memory")/(export "appmem")/' "$1" > "$B/rt-app-$n.wat"
sed 's/(import "mem"/(import "wasi2sys"/g' "$D/wat/sys2wasi.wat" > "$B/rt-sys2wasi.wat"
wat2wasm "$B/rt-app-$n.wat" -o "$B/rt-app-$n.wasm"
wat2wasm "$B/rt-sys2wasi.wat" -o "$B/rt-sys2wasi.wasm"
wat2wasm "$D/wat/wasi2sys.wat" -o "$B/wasi2sys.wasm"
wat2wasm "$D/../proc/wat/io.wat" -o "$B/io.wasm"
wasm-merge --skip-export-conflicts --enable-multimemory --enable-bulk-memory --enable-sign-ext \
  "$B/io.wasm" io "$B/rt-app-$n.wasm" app "$B/wasi2sys.wasm" wasi2sys "$B/rt-sys2wasi.wasm" sys \
  -o "$B/rt-$n.wasm"
echo "$B/rt-$n.wasm"
