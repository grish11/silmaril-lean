module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp.Main

/-!
# The remaining cases of the failure goal, after the first core instantiation with imports

`failRefWiredRest_of_rest'`: `Task.failRefWiredRest` (a failing node `k ≥ 1`, or a binary outside
`FirstCoreFrag`) from `Task.failRefWiredRest'` (a failing node `k ≥ 1`, or a binary outside
`FirstCoreFrag' = FirstCoreFrag ∨ FirstImpFrag`): the case `k = 0` in `FirstImpFrag` is
`firstImp_fail_ref`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp

open Silmaril.Wasm.Component Silmaril.Wasm.Component.DecoderBridge

open Silmaril.Wasm.Component.Conformance in
/-- **`Task.failRefWiredRest` from its remaining cases.** -/
theorem failRefWiredRest_of_rest' (h : Task.failRefWiredRest') : Task.failRefWiredRest := by
  intro b c r ps k hk hcase hc hr hv hw himp hn hready hfail
  by_cases hk0 : k = 0
  · by_cases hf : FirstImpFrag r
    · subst hk0
      exact firstImp_fail_ref hc hr hw hf himp hn hk hfail
    · refine h b c r ps k hk (.inr ?_) hc hr hv hw himp hn hready hfail
      rintro (hf' | hf')
      · rcases hcase with hk' | hn'
        · omega
        · exact hn' hf'
      · exact hf hf'
  · exact h b c r ps k hk (.inl (Nat.pos_of_ne_zero hk0)) hc hr hv hw himp hn hready hfail

end Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp
