#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../../.."
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
out=${1:-$work/results}
mkdir -p "$out"
out=$(realpath "$out")
export LEAN_PATH="$work${LEAN_PATH:+:$LEAN_PATH}"
lean() { timeout 30s lake env lean -j1 -M4096 -DautoImplicit=false -E warning --root="$work" "$@"; }

lake build --wfail +Silmaril.Wasm.Validation.Intrinsic.File +Silmaril.Wasm.Validation.Intrinsic.ReifyThms \
  +Silmaril.Wasm.Binary.Quote.Agreement +Silmaril.Wasm.Validation.Check.ValidateFinal

printf '\000asm\001\000\000\000\001\006\001\140\001\177\001\177\002\007\001\001h\001f\000\000\003\002\001\000\007\005\001\001g\000\001\012\010\001\006\000\040\000\020\000\013' \
  > "$work/host-call.wasm"
cp benchmarks/wasm-auto-verify/summaries/bin/sum8-closed.wasm "$work/sum8-closed.wasm"
{
  printf '\000asm\001\000\000\000\001\004\001\140\000\000\003\101\100'
  for _ in {1..64}; do printf '\000'; done
  printf '\012\201\002\100'
  for _ in {1..64}; do printf '\003\000\001\013'; done
} > "$work/bodies-64.wasm"
(cd "$work"; sha256sum host-call.wasm sum8-closed.wasm bodies-64.wasm) > "$out/fixtures.sha256"
(cd "$work"; sha256sum -c -) <<'HASHES'
a576d9a67f71c3a742f03585601b1b4d7fd90641f1b46bd2be66975570ee64f6  host-call.wasm
91a5a25f1151a8c6f1c3a55791270a1b354a127e2b9cc3d396370a22a4bcc3fb  sum8-closed.wasm
39f658cc097c6795dd899ec806c2131debdc92a52967adfc8825c160895f2a3c  bodies-64.wasm
HASHES

printf '\000asm\001' > "$work/malformed.wasm"
printf '\000asm\001\000\000\000' > "$work/empty.wasm"
printf '\000asm\001\000\000\000\001\004\001\140\000\000\003\002\001\000\012\006\001\004\000\101\000\013' \
  > "$work/ill-typed.wasm"
printf '\000asm\001\000\000\000\001\004\001\140\000\000\003\002\001\000\012\010\001\006\000\002\100\001\013\013' \
  > "$work/unsupported.wasm"

for fixture in malformed ill-typed unsupported; do
  printf 'module\nimport Silmaril.Wasm.Validation.Intrinsic.File\nwasm_intrinsic_file witness from "%s.wasm" with_raw raw\n' \
    "$fixture" > "$work/Rejected.lean"
  case "$fixture" in
    malformed) expected='malformed Core binary';;
    ill-typed) expected='ill-typed Core module (Core validator rejected it)';;
    unsupported) expected='well-typed Core module outside the supported intrinsic fragment';;
  esac
  if lean "$work/Rejected.lean" > "$out/$fixture.log" 2>&1 || ! rg -Fq "$expected" "$out/$fixture.log"; then
    cat "$out/$fixture.log"
    exit 1
  fi
done

cat > "$work/Classification.lean" <<'LEAN'
module
import Silmaril.Wasm.Binary.Quote.Defs
import Silmaril.Wasm.Validation.Intrinsic.Reify
import Silmaril.Wasm.Validation.Check.ValidateFinal

open Silmaril.Wasm.Validation

wasm_module validBlock from "unsupported.wasm"
wasm_module badBody from "ill-typed.wasm"

example : ModuleValid validBlock := validate_sound rfl
example : (Intrinsic.Reify.reify? validBlock).isSome = false := rfl
example : ¬ ModuleValid badBody := by
  intro valid
  have accepted := validate?_isSome_iff.mpr valid
  change false = true at accepted
  cases accepted
LEAN
lean "$work/Classification.lean" > "$out/classification.log" || { cat "$out/classification.log"; exit 1; }

cat > "$work/Example.lean" <<'LEAN'
module
public import Silmaril.Wasm.Validation.Intrinsic.File
public import Silmaril.Wasm.Binary.Quote.Defs

namespace IntrinsicFileExample

wasm_intrinsic_file witness from "host-call.wasm" with_raw raw with_source bytes
wasm_intrinsic_file withoutSource from "host-call.wasm" with_raw plain
wasm_module empty from "empty.wasm" with_source wrongBytes

end IntrinsicFileExample
LEAN
lean -o "$work/Example.olean" "$work/Example.lean"

printf 'case,phase,wall_s,peak_rss_kib\n' > "$out/timing.csv"
measure() {
  local fixture=$1 phase=$2
  shift 2
  /usr/bin/time -o "$out/time.tmp" -f '%e,%M' timeout 30s lake env lean -j1 -M4096 \
    -DautoImplicit=false -E warning --root="$work" "$@" > "$out/$fixture-$phase.log" 2>&1 || {
    cat "$out/$fixture-$phase.log"; exit 1;
  }
  printf '%s,%s,%s\n' "$fixture" "$phase" "$(cat "$out/time.tmp")" >> "$out/timing.csv"
}
for fixture in host-call sum8-closed bodies-64; do
  for form in raw intrinsic; do
    cat > "$work/Input.lean" <<'LEAN'
module
public import Silmaril.Wasm.Validation.Intrinsic.File
public import Silmaril.Wasm.Binary.Quote.Defs
LEAN
    if [[ $form = raw ]]; then
      printf 'wasm_module raw from "%s.wasm" with_source bytes\n' "$fixture" >> "$work/Input.lean"
    else
      printf 'wasm_intrinsic_file witness from "%s.wasm" with_raw raw with_source bytes\n' "$fixture" >> "$work/Input.lean"
    fi
    measure "$fixture" "$form-construction" -o "$work/Input.olean" "$work/Input.lean"
    printf 'module\nimport Input\nimport Silmaril.Wasm.Validation.Intrinsic.ReifyThms\n' > "$work/Consumer.lean"
    measure "$fixture" "$form-import" "$work/Consumer.lean"
    cp "$work/Consumer.lean" "$work/Query.lean"
    if [[ $fixture = bodies-64 ]]; then count=64; else count=1; fi
    if [[ $form = raw ]]; then
      printf 'example : raw.funcs.length = %s := rfl\n' "$count" >> "$work/Query.lean"
      printf 'example : Silmaril.Wasm.Validation.ModuleValid raw := Silmaril.Wasm.Validation.validate_sound rfl\n' \
        >> "$work/Consumer.lean"
    else
      printf 'example : witness.typed.funcs.erase.length = %s := rfl\n' "$count" >> "$work/Query.lean"
      cat >> "$work/Consumer.lean" <<'LEAN'
open Silmaril.Wasm.Validation
example : ModuleValid raw := ⟨witness.interface, witness.sound⟩
LEAN
    fi
    measure "$fixture" "$form-query" "$work/Query.lean"
    measure "$fixture" "$form-validity" "$work/Consumer.lean"
  done
  rm "$work/$fixture.wasm"
  cat > "$work/Agreement.lean" <<'LEAN'
module
public import Input
public import Silmaril.Wasm.Binary.Quote.Agreement

wasm_prove_source agrees : bytes => raw
LEAN
  measure "$fixture" source-agreement "$work/Agreement.lean"
done
rm "$work/empty.wasm" "$out/time.tmp"

cat > "$work/Imported.lean" <<'LEAN'
module
public import Example
public import Silmaril.Wasm.Binary.Quote.Agreement
public import Silmaril.Wasm.Validation.Intrinsic.ReifyThms
public import Silmaril.Wasm.Validation.Intrinsic.Quote

open IntrinsicFileExample Silmaril.Wasm.Validation Silmaril.Wasm.Binary

public theorem erasesExactly : witness.typed.erase = raw := witness.erase_eq
public theorem isWellTyped : ModuleOk raw witness.interface := witness.sound
wasm_prove_erasure explicitErasure : withoutSource.typed => plain
wasm_prove_source agrees : bytes => raw
public theorem sourceToIntrinsic : Core.decode? bytes.toByteArray = some witness.typed.erase :=
  agrees.trans (congrArg some erasesExactly.symm)

example : witness.interface.imports.length = 1 := rfl
example : raw.funcs.head?.map (·.body.length) = some 2 := rfl

#print axioms witness
#print axioms erasesExactly
#print axioms isWellTyped
#print axioms explicitErasure
#print axioms sourceToIntrinsic
LEAN
lean "$work/Imported.lean" > "$out/axioms.log" || { cat "$out/axioms.log"; exit 1; }
test "$(tr '\n' ' ' < "$out/axioms.log" | rg -o 'depends on axioms: \[propext, *Classical.choice, *Quot.sound\]|does not depend on any axioms' | wc -l)" -eq 5

cat > "$work/Wrong.lean" <<'LEAN'
module
public import Example
public import Silmaril.Wasm.Binary.Quote.Agreement
open IntrinsicFileExample
wasm_prove_source wrong : wrongBytes => raw
LEAN
if lean "$work/Wrong.lean" > "$out/wrong-source.log" 2>&1 ||
  ! rg -q '\(kernel\) (application|declaration) type mismatch' "$out/wrong-source.log"; then
  cat "$out/wrong-source.log"
  exit 1
fi
cat "$out/axioms.log" "$out/fixtures.sha256" "$out/timing.csv"
