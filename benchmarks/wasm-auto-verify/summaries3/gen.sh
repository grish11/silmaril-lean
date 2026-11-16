#!/usr/bin/env bash
# Regenerate the Binaryen output and the pinned binaries of the stage vcinfer benchmark
# (docs/projects/wasm-binaryen-tooling.md).
# Pinned tool: Binaryen wasm-opt version_123, from
#   https://github.com/WebAssembly/binaryen/releases/download/version_123/binaryen-version_123-x86_64-linux.tar.gz
#   bin/wasm-opt sha256 d66c6724c07334155720eb2def29c434dcaaf741ce859b4f7f389e22674f9c4a,
#   unpacked into ~/.cache/silmaril-tools/binaryen-123/ (see tools/wasm-egraph/tests/gen-tv.sh).
# max.wat is Silmaril/WasmSpec/Max's program; sum-decfirst.binaryen-O3.wat and sum-copy.binaryen-O3.wat are
# `wasm-opt X.wat -O3 -S`; the other WAT files are written by hand.
# Skips with a message when the pinned binary is absent.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
W="${BINARYEN_WASM_OPT:-$HOME/.cache/silmaril-tools/binaryen-123/binaryen-version_123/bin/wasm-opt}"
if [[ ! -x $W ]]; then
  echo "gen.sh: Binaryen wasm-opt version_123 not found at $W; skipping"
  exit 0
fi
sum=$(sha256sum "$W" | cut -d' ' -f1)
if [[ $sum != d66c6724c07334155720eb2def29c434dcaaf741ce859b4f7f389e22674f9c4a ]]; then
  echo "gen.sh: $W has sha256 $sum, not the pinned one; skipping"
  exit 0
fi
cd "$here"
for f in sum-decfirst sum-copy; do "$W" "$f.wat" -O3 -S -o "$f.binaryen-O3.wat"; done
mkdir -p bin
for f in *.wat; do
  "$W" "$f" -o "bin/${f%.wat}.wasm" 2>/dev/null
done
(cd bin && sha256sum ./*.wasm | sed 's# \./# #' > SHA256SUMS)
echo "gen.sh: ok"
