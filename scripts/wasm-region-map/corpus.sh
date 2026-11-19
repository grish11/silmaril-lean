#!/usr/bin/env bash
# Exactly seven checked-in binary fixtures; JSON is native measurement evidence.
set -euo pipefail
cd "$(dirname "$0")/../.."
python3 -I scripts/check-wasm-checkers.py >&2
exec .lake/build/bin/wasm-region-map \
  examples/wasm-checkers/lrat.wasm \
  examples/wasm-checkers/farkas.wasm \
  examples/wasm-acceptors/member_check.wasm \
  examples/wasm-acceptors/empty_check.wasm \
  examples/wasm-demos/rust-adder/wasm/adder.wasm \
  examples/wasm-demos/c-adder/wasm/adder.wasm \
  examples/wasm-demos/as-adder/wasm/adder.wasm
