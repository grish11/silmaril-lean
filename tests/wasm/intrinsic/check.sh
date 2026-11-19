#!/usr/bin/env bash
set -eu
cd "$(dirname "$0")/../../.."
source_dir="$PWD/tests/wasm/intrinsic"
build=$(mktemp -d)
trap 'rm -rf "$build"' EXIT
out=${1:-$build}
mkdir -p "$out"
export LEAN_PATH="$build${LEAN_PATH:+:$LEAN_PATH}"

lake build --wfail +Silmaril.Wasm.Validation.Intrinsic.Thms +Silmaril.Wasm.Validation.Intrinsic.Quote \
  +Silmaril.Wasm.Validation.Check.Validate
lean() { lake env lean -j1 -M4096 -DautoImplicit=false -E warning "$@"; }
measure() {
  local phase=$1
  shift
  /usr/bin/time -o "$out/timing.csv" -a -f "$phase,%e,%M" timeout -k 2 15 \
    lake env lean -j1 -M4096 -DautoImplicit=false -E warning "$@"
}
printf 'phase,wall_s,peak_rss_kib\n' > "$out/timing.csv"
measure raw-construction --root="$source_dir" -o "$build/RawExample.olean" "$source_dir/RawExample.lean"
measure intrinsic-construction --root="$source_dir" -o "$build/Example.olean" "$source_dir/Example.lean"
printf 'raw %s\nintrinsic %s\n' "$(wc -c < "$build/RawExample.olean")" "$(wc -c < "$build/Example.olean")" \
  > "$out/olean-bytes.txt"

for form in raw intrinsic; do
  if [ "$form" = raw ]; then
    printf 'module\npublic import RawExample\n\nopen WasmRawExample Silmaril.Wasm.Validation\n' > "$build/Imports.lean"
    value=raw
  else
    printf 'module\npublic import RawExample\npublic import Example\n\nopen WasmRawExample Silmaril.Wasm.Validation\n' > "$build/Imports.lean"
    value=WasmIntrinsicExample.intrinsic.erase
  fi
  measure "$form-import" "$build/Imports.lean"
  cp "$build/Imports.lean" "$build/Query.lean"
  printf '\nexample : (%s.funcs.head?.map (·.body.length)) = some 1 := rfl\n' "$value" >> "$build/Query.lean"
  measure "$form-query" "$build/Query.lean"
  cp "$build/Imports.lean" "$build/Proof.lean"
  if [ "$form" = raw ]; then
    printf '\nexample : ModuleOk raw interface := validate?_sound rfl\n' >> "$build/Proof.lean"
  else
    printf '\nexample : ModuleOk raw interface := by\n  have eq : %s = raw := rfl\n  exact eq ▸ WasmIntrinsicExample.intrinsic.sound\n' \
      "$value" >> "$build/Proof.lean"
  fi
  measure "$form-proof" "$build/Proof.lean"
done

lean "$source_dir/Regression.lean" > "$out/axioms.log" || { cat "$out/axioms.log"; exit 1; }
test "$(tr '\n' ' ' < "$out/axioms.log" | grep -Eo 'depends on axioms: \[propext, *Classical.choice, *Quot.sound\]|does not depend on any axioms' | wc -l)" -eq 4
cat "$out/axioms.log" "$out/timing.csv" "$out/olean-bytes.txt"
