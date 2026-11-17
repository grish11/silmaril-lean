# corpus/common.sh -- repository-authored helper, sourced by every <pkg>/build.sh and
# <pkg>/test.sh. Runs INSIDE the toolchain image (silmaril-corpus-toolchain:trixie-20251103).
# It fixes the environment (locale, timezone, SOURCE_DATE_EPOCH), selects the compiler for the
# target architecture, verifies cached archives, and records build facts for receipt.json.
set -euo pipefail
export LC_ALL=C TZ=UTC SOURCE_DATE_EPOCH=1762128000   # 2025-11-03T00:00:00Z (the image's date)
umask 022
CORPUS=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
CORPUS_CACHE=${CORPUS_CACHE:-/cache}
JOBS=${JOBS:-$(nproc)}

# setup_arch ARCH: CC/AR/... for x86_64 (native gcc) or aarch64 (Debian cross gcc); RUN runs a
# target program (empty natively, qemu-user for aarch64).
setup_arch() {
  ARCH=$1
  case "$ARCH" in
    x86_64)  TRIPLE=x86_64-linux-gnu; TP=; RUN=() ;;
    aarch64) TRIPLE=aarch64-linux-gnu; TP=aarch64-linux-gnu-
             RUN=(qemu-aarch64 -L /usr/aarch64-linux-gnu) ;;
    *) echo "unknown arch $ARCH (x86_64|aarch64)" >&2; exit 2 ;;
  esac
  CC=${TP}gcc; CXX=${TP}g++; AR=${TP}ar; RANLIB=${TP}ranlib; NM=${TP}nm; READELF=${TP}readelf
  OBJCOPY=${TP}objcopy; LD=${TP}ld
  export CC CXX AR RANLIB NM
}

# start_build PKG ARCH OUTDIR: fresh build directory /build/PKG, base flags, empty .build-info.
start_build() {
  PKG=$1; setup_arch "$2"; OUTDIR=$3
  BUILD=/build/$PKG
  rm -rf "$BUILD"; mkdir -p "$BUILD" "$OUTDIR"
  OUTDIR=$(cd "$OUTDIR" && pwd)
  rm -f "$OUTDIR/.build-info"
  # CORPUS_DEBUG_TWIN=1 (twin.sh): the same build with -g instead of -g0. GCC does not let -g change
  # the generated code, and twin.sh checks that: every object's .text and function symbols must be
  # byte-identical to the pinned object's. The twin's DWARF then maps functions to source.
  BASE_CFLAGS="-O2 $([ -n "${CORPUS_DEBUG_TWIN:-}" ] && echo -g || echo -g0) -ffile-prefix-map=$BUILD=."
  # CORPUS_SAVE_TEMPS=1 (frontend.sh): keep the preprocessed translation units (-save-temps=obj) and
  # copy every *.i under the build directory to OUTDIR/pp/ when the build ends.
  if [ -n "${CORPUS_SAVE_TEMPS:-}" ]; then
    BASE_CFLAGS="$BASE_CFLAGS -save-temps=obj"
    trap 'mkdir -p "$OUTDIR/pp"; (cd "$BUILD" && find . -name "*.i" -print0 | xargs -0 -r cp --parents -t "$OUTDIR/pp")' EXIT
  fi
  info arch "$ARCH"
  info build_dir "$BUILD"
}

# info KEY VALUE: one fact for receipt.json (key<TAB>value; keys may repeat)
info() { printf '%s\t%s\n' "$1" "$2" >> "$OUTDIR/.build-info"; }

# archive FILE SHA256 URL: path of a verified archive in $CORPUS_CACHE (fetched by fetch.sh)
archive() {
  local f=$CORPUS_CACHE/$1
  [ -f "$f" ] || { echo "$PKG: missing $f (run $PKG/fetch.sh with CORPUS_CACHE set)" >&2; exit 1; }
  echo "$2  $f" | sha256sum -c --quiet - >&2 || { echo "$PKG: $1: sha256 mismatch" >&2; exit 1; }
  info input "$3 $2"
  echo "$f"
}

# extract FILE DESTDIR: unpack a tar/zip archive (data only; nothing inside is executed here)
extract() {
  mkdir -p "$2"
  case "$1" in
    *.zip) unzip -q "$1" -d "$2" ;;
    *.txt) cp "$1" "$2/" ;;
    *) tar -C "$2" --no-same-owner -xf "$1" ;;
  esac
}

# collect ROOTDIR NAME: when CORPUS_COLLECT is set (maintainer mode, see build-all.sh --collect),
# copy every file listed on stdin (absolute paths under ROOTDIR) to $CORPUS_COLLECT/upstream/NAME/<rel>
# if it is byte-identical to the pristine archive copy (/build/pristine/NAME/<rel>, see pristine),
# else to $CORPUS_COLLECT/generated/<rel>. NAME may be empty (ROOTDIR then holds several archive roots).
collect() {
  [ -n "${CORPUS_COLLECT:-}" ] || { cat >/dev/null; return 0; }
  local root=$1 name=${2:-} p rel up
  while IFS= read -r p; do
    [ -f "$p" ] || continue
    rel=${p#"$root"/}
    [ "$rel" != "$p" ] || continue
    up=${name:+$name/}$rel
    if [ -f "/build/pristine/$up" ] && cmp -s "$p" "/build/pristine/$up"; then
      mkdir -p "$CORPUS_COLLECT/upstream/$(dirname "$up")"
      cp -p "$p" "$CORPUS_COLLECT/upstream/$up"
    else
      mkdir -p "$CORPUS_COLLECT/generated/$(dirname "$rel")"
      cp -p "$p" "$CORPUS_COLLECT/generated/$rel"
    fi
  done
}

# pristine FILE [SUBDIR]: unpack the archive again into /build/pristine[/SUBDIR] (collect mode only)
pristine() {
  [ -n "${CORPUS_COLLECT:-}" ] || return 0
  extract "$1" "/build/pristine${2:+/$2}"
}

# depfiles DIR...: absolute paths of the files named in the compiler depfiles (*.d, .deps/*.Po,
# .deps/*.Plo) found under DIR (or the given depfiles), resolved against the build root.
depfiles() { python3 -I "$CORPUS/depfiles.py" "$@"; }

# test helpers (test.sh): record COMMAND RESULT appends one JSON line to $TESTLOG
record() { python3 -I -c 'import json,sys; print(json.dumps({"command": sys.argv[1], "result": sys.argv[2]}))' "$1" "$2" >> "$TESTLOG"; }
# check DESC EXPECTED ACTUAL
check() {
  if [ "$2" = "$3" ]; then record "$1" "pass: $(printf %s "$3" | head -c 300)"
  else record "$1" "FAIL: expected [$(printf %s "$2" | head -c 200)] got [$(printf %s "$3" | head -c 200)]"; TEST_FAILED=1; fi
}
start_test() {  # start_test PKG ARCH OBJDIR
  PKG=$1; setup_arch "$2"; OBJ=$(cd "$3" && pwd); TESTLOG=$OBJ/.tests.jsonl; : > "$TESTLOG"; TEST_FAILED=0
  RUNS="${RUN[*]:-}"; RUNS=${RUNS:+$RUNS }
}
