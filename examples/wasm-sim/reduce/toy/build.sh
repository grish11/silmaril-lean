#!/bin/sh
# Build the toy artifact (toy.elf, committed; linked at 0x401000) and the native reference (toy-native).
set -e
cd "$(dirname "$0")"
out=${1:-build}
mkdir -p "$out"
if command -v clang >/dev/null 2>&1; then
  clang --target=x86_64-linux-gnu -c toy.S -o "$out/toy.o"
else
  as toy.S -o "$out/toy.o"   # GNU as: the same .text (scripts/check-wasm-sim.py checks it)
fi
ld -static -e f -Ttext=0x401000 "$out/toy.o" -o toy.elf
gcc -O1 toy.S native.c -o "$out/toy-native"
