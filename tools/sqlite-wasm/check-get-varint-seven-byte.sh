#!/usr/bin/env bash
set -euo pipefail

if [[ $# != 2 ]]; then
  echo "usage: $0 ARCHIVE_DIR WORK_DIR" >&2
  exit 2
fi
tool=$(dirname "$(realpath "$0")")
bash "$tool/check-get-varint-six-byte.sh" "$@"

root="$(realpath "$2")/lean"
src="$root/SqliteWasm"
cp "$tool"/{GetVarintSevenByte,GetVarintSevenByteImport}.lean "$src/"
cd "$tool/../.."
export LEAN_PATH="$root${LEAN_PATH:+:$LEAN_PATH}"
flags=(-j1 -s 131072 -DautoImplicit=false -E warning --root="$root")
lake env /usr/bin/time -f 'GetVarintSevenByte: %e s wall, %M KiB peak RSS' lean "${flags[@]}" \
  -o "$src/GetVarintSevenByte.olean" "$src/GetVarintSevenByte.lean"
lake env /usr/bin/time -f 'Ordinary import and replay: %e s wall, %M KiB peak RSS' lean "${flags[@]}" \
  "$src/GetVarintSevenByteImport.lean"
