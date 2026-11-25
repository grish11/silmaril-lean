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

if [[ $(basename "$src") != SqliteWasm || ! -f "$src/WholeModule.olean" ]]; then
  echo 'run the whole-module check in the generated SqliteWasm directory first' >&2
  exit 2
fi

lake build --wfail +Silmaril.Wasm.Execution.Core.Intrinsic.Thms \
  +Silmaril.Wasm.ModuleParts.Defs
cp "$tool/IntrinsicInitializer.lean" "$src/"
cp "$tool/ImportCheck.lean" "$src/IntrinsicInitializerImportCheck.lean"

export LEAN_PATH="$root${LEAN_PATH:+:$LEAN_PATH}"
for name in IntrinsicInitializer IntrinsicInitializerImportCheck; do
  file="$src/$name.lean"
  lake env /usr/bin/time -f "$name: %e s wall, %M KiB peak RSS" lean -j1 -s 131072 -M 6144 \
    -DautoImplicit=false -E warning --root="$root" -o "${file%.lean}.olean" "$file"
done
