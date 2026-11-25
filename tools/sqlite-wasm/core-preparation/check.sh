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

bash tools/sqlite-wasm/element-init/check.sh "$src"
lake build --wfail +Silmaril.Wasm.Execution.Core.Soundness.InstantiationAlloc
cp "$tool/PreparationBounds.lean" "$src/"
cp "$tool/CorePreparation.lean" "$src/"
cp "$tool/ImportCheck.lean" "$src/CorePreparationImportCheck.lean"

export LEAN_PATH="$root${LEAN_PATH:+:$LEAN_PATH}"
for name in PreparationBounds CorePreparation CorePreparationImportCheck; do
  file="$src/$name.lean"
  lake env /usr/bin/time -f "$name: %e s wall, %M KiB peak RSS" lean -j1 -s 131072 -M 6144 \
    -DautoImplicit=false -E warning --root="$root" -o "${file%.lean}.olean" "$file"
done
