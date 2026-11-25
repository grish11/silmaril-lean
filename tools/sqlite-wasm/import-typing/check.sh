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

bash tools/sqlite-wasm/element-init/check.sh "$src"
lake build --wfail +Silmaril.Wasm.Execution.Core.Exec.ExternAddrCheck
cp "$tool/ImportTyping.lean" "$src/"
cp "$tool/ImportCheck.lean" "$src/ImportTypingImportCheck.lean"

export LEAN_PATH="$root${LEAN_PATH:+:$LEAN_PATH}"
for name in ImportTyping ImportTypingImportCheck; do
  file="$src/$name.lean"
  lake env /usr/bin/time -f "$name: %e s wall, %M KiB peak RSS" lean -j1 -s 131072 -M 6144 \
    -DautoImplicit=false -E warning --root="$root" -o "${file%.lean}.olean" "$file"
done
