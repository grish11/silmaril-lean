#!/usr/bin/env bash
set -euo pipefail

if [[ $# != 2 ]]; then
  echo "usage: $0 ARCHIVE_DIR WORK_DIR" >&2
  exit 2
fi
tool=$(dirname "$(realpath "$0")")
bash "$tool/check-get-varint-five-byte.sh" "$@"

root="$(realpath "$2")/lean"
src="$root/SqliteWasm"
cp "$tool"/{GetVarintReaderSupport,GetVarintSixByte,GetVarintSixByteImport}.lean "$src/"
cd "$tool/../.."
export LEAN_PATH="$root${LEAN_PATH:+:$LEAN_PATH}"
flags=(-j1 -s 131072 -DautoImplicit=false -E warning --root="$root")
for name in GetVarintReaderSupport GetVarintSixByte; do
  lake env /usr/bin/time -f "$name: %e s wall, %M KiB peak RSS" lean "${flags[@]}" \
    -o "$src/$name.olean" "$src/$name.lean"
done
lake env /usr/bin/time -f 'Ordinary import and replay: %e s wall, %M KiB peak RSS' lean "${flags[@]}" \
  "$src/GetVarintSixByteImport.lean"
