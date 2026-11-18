#!/usr/bin/env bash
# corpus/build-all.sh -- build every corpus package for x86_64 and aarch64 in the pinned
# toolchain image and publish the ELF outputs under corpus/elf/<pkg>/<arch>/.
#
#   build-all.sh [PKG...]            fetch, build each arch twice from clean (fresh containers),
#                                    compare, run the package tests, write objects + receipt.json +
#                                    SHA256SUMS into corpus/elf
#   build-all.sh --check [PKG...]    build once per arch in a temp dir and compare every object with
#                                    the committed corpus/elf/<pkg>/<arch>/SHA256SUMS
#   build-all.sh --collect [PKG...]  maintainer mode: also refresh <pkg>/upstream/, upstream.sha256 and
#                                    <pkg>/generated/<arch>/ from the files the build read (depfiles)
#
# Env: CORPUS_CACHE (archive cache, default ~/.cache/silmaril-corpus), CORPUS_WORK (scratch, default a
# temp dir), JOBS. Docker has no bridge network on our hosts, hence --network host everywhere.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/.." && pwd)
TAG=silmaril-corpus-toolchain:trixie-20251103
BASE=debian:trixie-20251103@sha256:01a723bf5bfb21b9dda0c9a33e0538106e4d02cce8f557e118dd61259553d598
ALL=(sqlite cjson jemalloc mimalloc darkhttpd tcp-pingpong refcrypto coreutils openssl tinycc)
ARCHES=(x86_64 aarch64)
mode=build
case "${1:-}" in --check) mode=check; shift ;; --collect) mode=collect; shift ;; esac
pkgs=("$@"); [ ${#pkgs[@]} -gt 0 ] || pkgs=("${ALL[@]}")
export CORPUS_CACHE=${CORPUS_CACHE:-$HOME/.cache/silmaril-corpus}
mkdir -p "$CORPUS_CACHE"
work=${CORPUS_WORK:-$(mktemp -d)}; mkdir -p "$work"
docker image inspect "$TAG" >/dev/null 2>&1 || "$here/toolchain/image.sh" >/dev/null
IMAGE_ID=$(docker image inspect --format '{{.Id}}' "$TAG")

dr() {  # dr OUTDIR [extra docker args...] -- CMD...: run CMD in the image
  local out=$1; shift; local extra=()
  while [ "$1" != -- ]; do extra+=("$1"); shift; done; shift
  docker run --rm --network host --cpus 8 --memory 32g -e JOBS="${JOBS:-8}" -e SOURCE_DATE_EPOCH=1762128000 \
    -v "$here:/corpus:ro" -v "$CORPUS_CACHE:/cache:ro" -v "$out:/out" "${extra[@]}" "$TAG" "$@"
}
objsums() { (cd "$1" && find . -maxdepth 1 -type f ! -name '.*' ! -name receipt.json ! -name SHA256SUMS -printf '%f\n' | sort | xargs -r sha256sum); }

fail=0
for pkg in "${pkgs[@]}"; do
  echo "== $pkg: fetch" >&2
  "$here/$pkg/fetch.sh"
  [ $mode = collect ] && rm -rf "$here/$pkg/upstream" "$here/$pkg/generated"
  for arch in "${ARCHES[@]}"; do
    w=$work/$pkg/$arch; rm -rf "$w"; mkdir -p "$w/a" "$w/b"
    if [ $mode = check ]; then
      echo "== $pkg/$arch: build" >&2
      dr "$w/a" -- bash "/corpus/$pkg/build.sh" "$arch" /out > "$w/a.log" 2>&1 || { echo "build failed: $w/a.log" >&2; fail=1; continue; }
      want=$repo/corpus/elf/$pkg/$arch/SHA256SUMS
      if diff <(objsums "$w/a" | sed 's#  \./#  #') "$want" >&2; then echo "check $pkg/$arch ok" >&2
      else echo "check $pkg/$arch: MISMATCH" >&2; fail=1; fi
      continue
    fi
    for r in a b; do
      echo "== $pkg/$arch: build $r" >&2
      extra=()
      if [ $mode = collect ] && [ $r = a ]; then mkdir -p "$w/collect"; extra=(-v "$w/collect:/collect" -e CORPUS_COLLECT=/collect); fi
      dr "$w/$r" "${extra[@]}" -- bash "/corpus/$pkg/build.sh" "$arch" /out > "$w/$r.log" 2>&1 \
        || { echo "build $r failed, log: $w/$r.log" >&2; tail -30 "$w/$r.log" >&2; exit 1; }
    done
    repro=false
    if [ "$(objsums "$w/a")" = "$(objsums "$w/b")" ]; then repro=true; else
      echo "$pkg/$arch: NOT reproducible" >&2; diff <(objsums "$w/a") <(objsums "$w/b") >&2 || true; fi
    echo "== $pkg/$arch: test" >&2
    dr "$w/a" -- bash "/corpus/$pkg/test.sh" "$arch" /out > "$w/test.log" 2>&1 || { echo "$pkg/$arch: tests reported failure ($w/test.log)" >&2; fail=1; }
    dr "$w/a" -- python3 -I /corpus/receipt.py "/corpus/$pkg" "$arch" /out "$repro" "$TAG" "$IMAGE_ID" "$BASE"
    dest=$repo/corpus/elf/$pkg/$arch
    rm -rf "$dest"; mkdir -p "$dest"
    find "$w/a" -maxdepth 1 -type f ! -name '.*' -exec cp -p {} "$dest/" \;
    cat "$dest/SHA256SUMS" >&2
    if [ $mode = collect ]; then
      mkdir -p "$here/$pkg/upstream"
      [ -d "$w/collect/upstream" ] && cp -a "$w/collect/upstream/." "$here/$pkg/upstream/"
      rm -rf "$here/$pkg/generated/$arch"
      if [ -d "$w/collect/generated" ]; then
        mkdir -p "$here/$pkg/generated/$arch"; cp -a "$w/collect/generated/." "$here/$pkg/generated/$arch/"
        printf '%s\n' "GENERATED FILES -- not upstream sources, not hand-written." \
          "Produced in /build/$pkg by the $arch build (build.sh $arch): configure/build-generated sources and" \
          "headers that the compiler read (from the depfiles) and that are absent from, or differ from, the" \
          "pinned upstream archive. Refresh with: corpus/build-all.sh --collect $pkg" > "$here/$pkg/generated/$arch/GENERATED.txt"
      fi
    fi
  done
  if [ $mode = collect ]; then
    (cd "$here/$pkg" && find upstream -type f | LC_ALL=C sort | xargs -d '\n' sha256sum > upstream.sha256)
  fi
done
[ $mode = check ] || python3 -I "$here/mktable.py" "$repo" || fail=1
exit $fail
