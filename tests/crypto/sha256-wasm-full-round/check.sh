#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../../.."
test_dir=tests/crypto/sha256-wasm-full-round
lake=${LAKE:-lake}

"$lake" build --wfail +Silmaril.Wasm.Examples.Sha256FullRound.Thms
if [[ "${1:-}" == --lean-only ]]; then
  "$lake" env lean -DautoImplicit=false -DwarningAsError=true "$test_dir/Check.lean"
  exit 0
fi

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
clang-19 --target=wasm32-unknown-unknown -O2 -ffreestanding -nostdlib \
  -Wl,--no-entry,--strip-all,--export=sha256_round \
  tests/crypto/sha256-wasm/round.c "$test_dir/e.c" "$test_dir/round.c" -o "$tmp/round.wasm"
printf '%s  %s\n' ba4cd633daba887fbd53053f57ea5729c6ba96ca5e0c89ae5d877be9ad136c8e \
  "$tmp/round.wasm" | sha256sum --check
"$lake" env lean -DautoImplicit=false -DwarningAsError=true --run "$test_dir/Check.lean" "$tmp/round.wasm"
node "$test_dir/kat.mjs" "$tmp/round.wasm"
