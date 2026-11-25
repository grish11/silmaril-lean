#!/usr/bin/env bash
set -euo pipefail

if [[ $# != 2 && $# != 3 ]]; then
  echo "usage: $0 ARCHIVE_DIR {OUTPUT.wasm [OUTPUT.map] | --retain-llvm DIR}" >&2
  exit 2
fi
archives=$(realpath "$1")
link_map=()
retain=
stages=()
if [[ $2 == --retain-llvm ]]; then
  if [[ $# != 3 ]]; then
    echo "--retain-llvm requires an output directory" >&2
    exit 2
  fi
  retain=$(realpath -m "$3")
  output=$retain/sqlite3.wasm
  map=$retain/sqlite3.map
  link_map=(-Wl,--Map=sqlite3.map)
  stages=(-save-temps=obj)
else
  output=$(realpath -m "$2")
fi
if [[ $# == 3 && -z $retain ]]; then
  map=$(realpath -m "$3")
  if [[ "$map" == "$output" ]]; then
    echo "Wasm and link map paths must differ" >&2
    exit 2
  fi
  link_map=(-Wl,--Map=sqlite3.map)
fi
manifest=$(dirname "$(realpath "$0")")/artifact.sha256
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

(
  cd "$archives"
  sha256sum --check <<'HASHES'
0a9c8e34352dad46006aa82836d5383bff9dc6bc9ce5a60553c05aa30e6ad1f9  sqlite-amalgamation-3540100.zip
0507679dff16814b74516cd969a9b16d2ced1347388024bc7966264648c78bfb  wasi-sdk-30.0-x86_64-linux.tar.gz
HASHES
)
unzip -q "$archives/sqlite-amalgamation-3540100.zip" -d "$tmp"
tar -xzf "$archives/wasi-sdk-30.0-x86_64-linux.tar.gz" -C "$tmp"
(
  # Clang reports physical paths even when TMPDIR is reached through a symlink.
  cd -P "$tmp"
  sha256sum --check <<'HASHES'
0c657666d819f261cc4007526ad57e1669de9949df7a8ea847aa284a2bf0ee52  sqlite-amalgamation-3540100/sqlite3.c
a5431c3533853c135005e2d6e32b211e7921c9255e69f34d5557a319c24a6169  wasi-sdk-30.0-x86_64-linux/bin/clang
57ca1189824aed3afefcbecb778ca5f0f0a7a7f0abf3666940275b94b9435e7d  wasi-sdk-30.0-x86_64-linux/bin/wasm-ld
HASHES
  sdk=wasi-sdk-30.0-x86_64-linux/bin
  driver=("$sdk/clang"
    -Os -mexec-model=reactor "${stages[@]}"
    -DSQLITE_THREADSAFE=0 -DSQLITE_OMIT_LOAD_EXTENSION -DSQLITE_OMIT_WAL -DSQLITE_TEMP_STORE=3
    -Wl,--strip-all "${link_map[@]}" -Wl,--export=sqlite3_libversion_number
    -Wl,--export=sqlite3_open -Wl,--export=sqlite3_prepare_v2 -Wl,--export=sqlite3_step
    -Wl,--export=sqlite3_column_int -Wl,--export=sqlite3_finalize -Wl,--export=sqlite3_close
    -Wl,--export=malloc -Wl,--export=free sqlite-amalgamation-3540100/sqlite3.c -o sqlite3.wasm)
  if [[ -n $retain ]]; then
    export LC_ALL=C SOURCE_DATE_EPOCH=1641013200
    trace=$("${driver[@]}" -### 2>&1)
    {
      printf 'LC_ALL=%s SOURCE_DATE_EPOCH=%s' "$LC_ALL" "$SOURCE_DATE_EPOCH"
      printf ' %q' "${driver[@]}"
      printf '\n%s\n' "${trace//"$PWD"/<build>}"
      "$sdk/wasm-ld" --version
      "$sdk/llvm-nm" --version
    } > clang-stages.txt
  fi
  "${driver[@]}"
  sha256sum --check "$manifest"
  if [[ -n $retain ]]; then
    for stage in bc o; do
      "$sdk/llvm-nm" --defined-only --format=posix "sqlite3.$stage" > "sqlite3.$stage.symbols"
    done
  fi
)
if [[ -n $retain ]]; then
  mkdir -p "$retain"
  install -m 0644 "$tmp"/{sqlite3.bc,sqlite3.o,sqlite3.bc.symbols,sqlite3.o.symbols,clang-stages.txt} "$retain/"
fi
install -m 0644 "$tmp/sqlite3.wasm" "$output"
if [[ $# == 3 ]]; then
  install -m 0644 "$tmp/sqlite3.map" "$map"
fi
