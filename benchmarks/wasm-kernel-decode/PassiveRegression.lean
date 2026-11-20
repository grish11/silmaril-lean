module

public import Silmaril.Wasm.Binary.Packed.Passive.Thms
public import Silmaril.Prelude.Bytes.Elab.Defs

open Silmaril.Wasm.Binary.Packed

namespace WasmPassiveRegression

kbytes_def source of_chunks 1 15 [0, 97, 115, 109, 1, 0, 0, 0, 11, 5, 1, 1, 2, 42, 127]
kbytes_def payload of_chunks 1 2 [42, 127]
kbytes_def different of_chunks 1 2 [42, 0]
kbytes_def truncated of_chunks 1 14 [0, 97, 115, 109, 1, 0, 0, 0, 11, 5, 1, 1, 2, 42]

@[expose] public def plan : PassivePlan := ⟨10, 11, 12, 13⟩

theorem checked : plan.Verified source source.wf_true payload where
  sectionPresent := by decide +kernel
  countFits := by decide +kernel
  consumesInput := rfl
  header := rfl
  id := rfl
  size := rfl
  count := rfl
  mode := rfl
  length := rfl
  payloadMatches := rfl

theorem fullAgreement : Silmaril.Wasm.Binary.Core.decode? source.toByteArray =
    some { data := [⟨payload.toByteArray, .passive⟩] } := checked.sound payload.wf_true

example : ¬ plan.Verified source source.wf_true different := by
  intro bad
  have mismatch : (source.slice plan.payloadStart different.len).sameBytes 4096 different = false := rfl
  have payloadEq := bad.payloadMatches
  rw [mismatch] at payloadEq
  exact Bool.noConfusion payloadEq

example : ¬ plan.Verified truncated truncated.wf_true payload := by
  intro bad
  have finishes : plan.payloadStart + payload.len = 14 := bad.consumesInput
  cases finishes

#print axioms fullAgreement

end WasmPassiveRegression
