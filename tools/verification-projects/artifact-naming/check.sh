#!/usr/bin/env bash
set -euo pipefail
if (( $# > 2 )); then
  echo 'usage: check.sh [manifest [serialized-title-output]]' >&2
  exit 2
fi
manifest=${1:-}
output=${2:-}
[[ -z "$manifest" || "$manifest" = /* ]] || manifest="$PWD/$manifest"
[[ -z "$output" || "$output" = /* ]] || output="$PWD/$output"
tool=$(cd "$(dirname "$0")" && pwd)
cd "$tool/../../.."
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

python3 -BEs "$tool/import_lean.py" "${manifest:-$tool/fixtures.tsv}" > "$work/ArtifactNamingRows.lean"
(cd "$work" && lean -DwarningAsError=true -o ArtifactNamingRows.olean ArtifactNamingRows.lean)
export LEAN_PATH="$work${LEAN_PATH:+:$LEAN_PATH}"
if [[ -n "$output" ]]; then
  lake env lean -DwarningAsError=true --run tests/formats/ArtifactNaming.lean "$output"
else
  lake env lean -DwarningAsError=true tests/formats/ArtifactNaming.lean
fi
