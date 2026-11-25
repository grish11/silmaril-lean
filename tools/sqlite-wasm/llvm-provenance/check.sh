#!/usr/bin/env bash
set -euo pipefail

if [[ $# != 1 ]]; then
  echo "usage: $0 ARCHIVE_DIR" >&2
  exit 2
fi
here=$(dirname "$(realpath "$0")")
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
mkdir "$work/physical"
ln -s physical "$work/symlinked temp"
for pass in first second; do
  stage=$work/$pass
  scratch=$work/physical
  if [[ $pass == second ]]; then
    scratch="$work/symlinked temp"
  fi
  if ! TMPDIR="$scratch" timeout 90 bash "$here/../build.sh" "$1" --retain-llvm "$stage" > "$work/$pass.log" 2>&1; then
    cat "$work/$pass.log" >&2
    exit 1
  fi
  python3 -B "$here/receipt.py" "$1" "$stage" > "$stage/receipt.json"
  diff -u "$here/clang-stages.txt" "$stage/clang-stages.txt"
  diff -u "$here/receipt.json" "$stage/receipt.json"
done
for artifact in sqlite3.bc sqlite3.o sqlite3.wasm; do
  cmp "$work/first/$artifact" "$work/second/$artifact"
done
echo "Two clean builds reproduce the LLVM receipt and all three stage artifacts."
