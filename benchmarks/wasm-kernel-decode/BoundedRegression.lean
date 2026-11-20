module

import Silmaril.Prelude.Bytes.Elab.Defs
public import Silmaril.Wasm.Binary.Packed.Bounded.Thms

open Silmaril.Wasm.Binary Silmaril.Wasm.Binary.Packed

namespace WasmBoundedRegression

kbytes_def headerOnly of_chunks 1 8 [0, 97, 115, 109, 1, 0, 0, 0]
kbytes_def oneFunction of_chunks 1 24
  [0, 97, 115, 109, 1, 0, 0, 0, 1, 4, 1, 96, 0, 0, 3, 2, 1, 0, 10, 4, 1, 2, 0, 11]
kbytes_def shortType of_chunks 1 15
  [0, 97, 115, 109, 1, 0, 0, 0, 1, 3, 1, 96, 0, 0, 0]
kbytes_def shortCode of_chunks 1 24
  [0, 97, 115, 109, 1, 0, 0, 0, 1, 4, 1, 96, 0, 0, 3, 2, 1, 0, 10, 4, 1, 1, 0, 11]
kbytes_def cutCodeLeb of_chunks 1 15
  [0, 97, 115, 109, 1, 0, 0, 0, 10, 2, 1, 128, 11, 1, 0]
kbytes_def badLeb of_chunks 1 14
  [0, 97, 115, 109, 1, 0, 0, 0, 1, 128, 128, 128, 128, 16]
kbytes_def missingCode of_chunks 1 18
  [0, 97, 115, 109, 1, 0, 0, 0, 1, 4, 1, 96, 0, 0, 3, 2, 1, 0]
kbytes_def wrongDataCount of_chunks 1 11
  [0, 97, 115, 109, 1, 0, 0, 0, 12, 1, 1]
kbytes_def exactDataCount of_chunks 1 11
  [0, 97, 115, 109, 1, 0, 0, 0, 12, 1, 0]
kbytes_def repeatedType of_chunks 1 14
  [0, 97, 115, 109, 1, 0, 0, 0, 1, 1, 0, 1, 1, 0]
kbytes_def validCustom of_chunks 1 11
  [0, 97, 115, 109, 1, 0, 0, 0, 0, 1, 0]

example : Bounded.decode? shortType shortType.wf_true = none := rfl
example : Bounded.decode? shortCode shortCode.wf_true (some [4]) = none := rfl
example : Bounded.decode? cutCodeLeb cutCodeLeb.wf_true (some [2]) = none := rfl
example : Bounded.decode? oneFunction oneFunction.wf_true (some [3]) = none := rfl
example : Bounded.decode? oneFunction oneFunction.wf_true (some [5]) = none := rfl
example : Bounded.decode? oneFunction oneFunction.wf_true (some []) = none := rfl
example : Bounded.decode? oneFunction oneFunction.wf_true (some [4, 4]) = none := rfl
example : Bounded.decode? badLeb badLeb.wf_true = none := rfl
example : Bounded.decode? missingCode missingCode.wf_true = none := rfl
example : Bounded.decode? wrongDataCount wrongDataCount.wf_true = none := rfl
example : Bounded.decode? validCustom validCustom.wf_true = none := rfl
example : Core.decode? validCustom.toByteArray = some {} := rfl
example : Bounded.decode? repeatedType repeatedType.wf_true = none := rfl
example : Core.decode? exactDataCount.toByteArray = some {} :=
  Bounded.decode_sound (wf := exactDataCount.wf_true) (show Bounded.decode? _ _ = some {} from rfl)
example : Core.decode? headerOnly.toByteArray = some {} :=
  Bounded.decode_sound (wf := headerOnly.wf_true) (show Bounded.decode? _ _ = some {} from rfl)

@[expose] public def expected : Silmaril.Wasm.Module := {
  types := [⟨[⟨true, [], .func ⟨[], []⟩⟩]⟩]
  funcs := [⟨⟨⟨0, by decide⟩⟩, [], []⟩]
}

public theorem exactDecode : Core.decode? oneFunction.toByteArray = some expected :=
  Bounded.decode_sound (wf := oneFunction.wf_true)
    (show Bounded.decode? _ _ (some [4]) = some expected from rfl)

#print axioms exactDecode
#print axioms Bounded.decode_sound

end WasmBoundedRegression
