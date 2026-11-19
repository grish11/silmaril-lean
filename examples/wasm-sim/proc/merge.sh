#!/bin/sh
# Merged variant: wasm-merge all core modules of the stack into ONE module per simulator
# (build/merged-$s.wasm), and a wasm-opt -O3 version (cross-module inlining).
#   cd progs && wasmtime run --dir . ../build/merged-g.wasm dyn a b
set -eu
cd "$(dirname "$0")/build"
F="--enable-multimemory --enable-bulk-memory --enable-reference-types --enable-sign-ext --enable-mutable-globals"
for s in mini g m; do
  [ -f x86-$s.wasm ] || continue
  wasm-merge $F --rename-export-conflicts io.wasm io mem.wasm mem sys.wasm sys stubs.wasm nd \
    stubs.wasm ext libc.wasm ffi x86-$s.wasm core extrun.wasm sim loader.wasm loader -o merged-$s.wasm
  wasm-opt $F -O3 merged-$s.wasm -o merged-$s-O3.wasm
done
