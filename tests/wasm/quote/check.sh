#!/usr/bin/env bash
set -eu
cd "$(dirname "$0")/../../.."
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

lake build --wfail +Silmaril.Wasm.Binary.Quote.Agreement +Silmaril.Wasm.Validation.Check.Validate
export LEAN_PATH="$work${LEAN_PATH:+:$LEAN_PATH}"
lean() { lake env lean -j1 -DautoImplicit=false -E warning --root="$work" "$@"; }

cp examples/wasm-acceptors/empty_check.wasm "$work/good.wasm"
printf '\000asm\001' > "$work/malformed.wasm"
printf '\000asm\001\000\000\000' > "$work/empty.wasm"
printf '\000asm\001\000\000\000\001\004\001\140\000\000\003\002\001\000\012\006\001\004\000\101\000\013' \
  > "$work/ill-typed.wasm"

cat > "$work/QuotedFixture.lean" <<'EOF'
module
public import Silmaril.Wasm.Binary.Quote.Defs

namespace QuotedFixture

wasm_module result from "good.wasm" with_source bytes
wasm_module unvalidated from "ill-typed.wasm" with_source unvalidatedBytes
wasm_module empty from "empty.wasm" with_source differentBytes
wasm_module onlyModule from "good.wasm"

example : (wasm_module% "good.wasm").funcs.head?.isSome = true := rfl
example : onlyModule = result := rfl

end QuotedFixture
EOF
lean -o "$work/QuotedFixture.olean" "$work/QuotedFixture.lean"
rm "$work/good.wasm" "$work/ill-typed.wasm" "$work/empty.wasm"

cat > "$work/Imported.lean" <<'EOF'
module
public import QuotedFixture
public import Silmaril.Wasm.Binary.Quote.Agreement
import Silmaril.Wasm.Validation.Check.Validate

open QuotedFixture Silmaril.Wasm.Validation

example : result.funcs.head?.isSome = true := rfl
wasm_prove_source agrees : bytes => result
wasm_prove_source unvalidatedAgrees : unvalidatedBytes => unvalidated
example : (validate? unvalidated).isSome = false := by decide +kernel

#print axioms agrees
#print axioms unvalidatedAgrees
EOF
lean "$work/Imported.lean" > "$work/audit.log" || { cat "$work/audit.log"; exit 1; }
cat "$work/audit.log"
test "$(grep -Ec 'depends on axioms: \[propext, Classical.choice, Quot.sound\]|does not depend on any axioms' "$work/audit.log")" -eq 2

cat > "$work/Wrong.lean" <<'EOF'
module
public import QuotedFixture
public import Silmaril.Wasm.Binary.Quote.Agreement
open QuotedFixture
wasm_prove_source wrong : differentBytes => result
EOF
if lean "$work/Wrong.lean" > "$work/wrong.log" 2>&1 ||
   ! grep -Eq '\(kernel\) (application|declaration) type mismatch' "$work/wrong.log"; then
  cat "$work/wrong.log"
  exit 1
fi

cat > "$work/Malformed.lean" <<'EOF'
module
import Silmaril.Wasm.Binary.Quote.Defs
wasm_module broken from "malformed.wasm"
EOF
if lean "$work/Malformed.lean" > "$work/malformed.log" 2>&1 ||
   ! grep -Fq 'wasm_module: decoder: 8 bytes requested past the end' "$work/malformed.log"; then
  cat "$work/malformed.log"
  exit 1
fi
echo 'Wasm quotation: import, agreement, wrong source, malformed file, and validation separation passed.'
