# corpus/fetch-lib.sh -- repository-authored helper sourced by every <pkg>/fetch.sh (host side;
# needs curl and sha256sum). fetch URL FILE SHA256: download URL to $CORPUS_CACHE/FILE unless present,
# then verify its sha256.
set -euo pipefail
CORPUS_CACHE=${CORPUS_CACHE:-$HOME/.cache/silmaril-corpus}
mkdir -p "$CORPUS_CACHE"
fetch() {
  local url=$1 file=$2 sha=$3 f=$CORPUS_CACHE/$2
  if [ ! -f "$f" ]; then curl -fsSL --retry 3 -o "$f.part" "$url"; mv "$f.part" "$f"; fi
  echo "$sha  $f" | sha256sum -c --quiet - || { echo "fetch: $file: sha256 mismatch (expected $sha)" >&2; exit 1; }
  echo "fetched $file" >&2
}
