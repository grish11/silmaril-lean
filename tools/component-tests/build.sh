#!/usr/bin/env bash
# Assemble the component test binaries (examples/component-tests/*.wat) with the pinned
# wasm-tools 1.262.0 (tools/wasm-tools/tests/pins.sh; installed by its fetch-pins.sh), strip
# every custom section (names), validate, and compare with the committed .wasm files.
#
#   tools/component-tests/build.sh           # check: the committed binaries are reproduced
#   tools/component-tests/build.sh --write   # rewrite the .wasm files
#
# Not run in CI (it needs the pinned tool); the Lean modules read the committed .wasm files.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
. "$root/tools/wasm-tools/tests/pins.sh"
[ -x "$WT_UPSTREAM" ] || { echo "build: $WT_UPSTREAM missing (tools/wasm-tools/tests/fetch-pins.sh)" >&2; exit 2; }
echo "$WT_UPSTREAM_SHA256  $WT_UPSTREAM" | sha256sum -c --quiet - \
  || { echo "build: wasm-tools SHA-256 mismatch" >&2; exit 2; }
dir=$root/examples/component-tests
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
status=0
for wat in "$dir"/*.wat; do
  n=$(basename "$wat" .wat)
  "$WT_UPSTREAM" parse "$wat" -o "$tmp/$n.named.wasm"
  "$WT_UPSTREAM" strip --all "$tmp/$n.named.wasm" -o "$tmp/$n.wasm"
  "$WT_UPSTREAM" validate "$tmp/$n.wasm"
  if [ "${1:-}" = --write ]; then
    cp "$tmp/$n.wasm" "$dir/$n.wasm"
  elif ! cmp -s "$tmp/$n.wasm" "$dir/$n.wasm"; then
    echo "build: $n.wasm differs from the assembled $n.wat" >&2; status=1
  fi
  printf '%s  %s (%s bytes)\n' "$(sha256sum < "$tmp/$n.wasm" | cut -d' ' -f1)" "$n.wasm" \
    "$(stat -c %s "$tmp/$n.wasm")"
done
exit $status
