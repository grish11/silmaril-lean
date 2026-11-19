#!/bin/sh
# Build the Wasm modules (wat2wasm) into build/, and the x86-64 test programs in progs/.
set -eu
cd "$(dirname "$0")"
mkdir -p build
for f in wat/*.wat; do
  wat2wasm "$f" -o "build/$(basename "$f" .wat).wasm"
done
# the x86-64 simulators (G and M state representations), if present
for s in g m; do
  [ -f ../x86/x86-$s.wat ] && wat2wasm ../x86/x86-$s.wat -o build/x86-$s.wasm
done
progs/build.sh
