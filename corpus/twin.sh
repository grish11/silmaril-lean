#!/usr/bin/env bash
# corpus/twin.sh [PKG...] -- build each package's debug twin (CORPUS_DEBUG_TWIN=1: -g instead of
# -g0, nothing else changed) for x86_64 and aarch64 in the pinned image, and write the function
# map corpus/<pkg>/funcmap/<arch>/<object>.json (funcmap.py) for every pinned object. The map is
# written only from a twin whose .text and function symbols equal the pinned object's; the twin
# itself is not kept.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
TAG=silmaril-corpus-toolchain:trixie-20251103
ALL=(sqlite cjson jemalloc mimalloc darkhttpd tcp-pingpong refcrypto coreutils openssl tinycc)
pkgs=("$@"); [ ${#pkgs[@]} -gt 0 ] || pkgs=("${ALL[@]}")
export CORPUS_CACHE=${CORPUS_CACHE:-$HOME/.cache/silmaril-corpus}
work=${CORPUS_WORK:-$(mktemp -d)}
for pkg in "${pkgs[@]}"; do
  "$here/$pkg/fetch.sh"
  for arch in x86_64 aarch64; do
    w=$work/twin/$pkg/$arch; rm -rf "$w"; mkdir -p "$w"
    docker run --rm --network host -e CORPUS_DEBUG_TWIN=1 -e SOURCE_DATE_EPOCH=1762128000 \
      -v "$here:/corpus:ro" -v "$CORPUS_CACHE:/cache:ro" -v "$w:/out" "$TAG" bash "/corpus/$pkg/build.sh" "$arch" /out > "$w.log" 2>&1 \
      || { echo "twin build failed: $w.log" >&2; exit 1; }
    mkdir -p "$here/$pkg/funcmap/$arch"
    while read -r _ obj; do
      docker run --rm --network host -v "$here:/corpus" -v "$w:/twin:ro" "$TAG" \
        python3 -I /corpus/funcmap.py "$arch" "/corpus/elf/$pkg/$arch/$obj" "/twin/$obj" "/corpus/$pkg/funcmap/$arch/$obj.json"
    done < "$here/elf/$pkg/$arch/SHA256SUMS"
  done
done
