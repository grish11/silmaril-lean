#!/usr/bin/env bash
set -euo pipefail

if [[ $# != 1 ]]; then
  echo "usage: $0 QUOTED_SQLITEWASM_DIR" >&2
  exit 2
fi
src=$(realpath "$1")
root=$(dirname "$src")
tool=$(dirname "$(realpath "$0")")
cd "$tool/../../.."

for prerequisite in intrinsic-initializer initializer-flag wasi-thread-setup startup-bindings; do
  bash "tools/sqlite-wasm/$prerequisite/check.sh" "$src"
done

cp "$tool/InitializerStartup.lean" "$src/"
cp "$tool/ImportCheck.lean" "$src/InitializerStartupImportCheck.lean"

export LEAN_PATH="$root${LEAN_PATH:+:$LEAN_PATH}"
for name in InitializerStartup InitializerStartupImportCheck; do
  file="$src/$name.lean"
  lake env /usr/bin/time -f "$name: %e s wall, %M KiB peak RSS" lean -j1 -s 131072 -M 6144 \
    -DautoImplicit=false -E warning --root="$root" -o "${file%.lean}.olean" "$file"
done
