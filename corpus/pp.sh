#!/usr/bin/env bash
# corpus/pp.sh OUTDIR [PKG...] -- build each package with -save-temps (CORPUS_SAVE_TEMPS=1) for
# x86_64 and aarch64 and keep its preprocessed translation units in OUTDIR/<pkg>/<arch>/pp/.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
out=$1; shift
TAG=silmaril-corpus-toolchain:trixie-20251103
ALL=(sqlite cjson jemalloc mimalloc darkhttpd tcp-pingpong refcrypto coreutils openssl tinycc)
pkgs=("$@"); [ ${#pkgs[@]} -gt 0 ] || pkgs=("${ALL[@]}")
export CORPUS_CACHE=${CORPUS_CACHE:-$HOME/.cache/silmaril-corpus}
for pkg in "${pkgs[@]}"; do for arch in x86_64 aarch64; do
  w=$out/$pkg/$arch; rm -rf "$w"; mkdir -p "$w"
  docker run --rm --network host -e CORPUS_SAVE_TEMPS=1 -e SOURCE_DATE_EPOCH=1762128000 \
    -v "$here:/corpus:ro" -v "$CORPUS_CACHE:/cache:ro" -v "$w:/out" "$TAG" bash "/corpus/$pkg/build.sh" "$arch" /out > "$w.log" 2>&1 \
    || echo "pp build failed: $pkg/$arch ($w.log)" >&2
  echo "$pkg/$arch: $(find "$w/pp" -name '*.i' 2>/dev/null | wc -l) translation units" >&2
done; done
