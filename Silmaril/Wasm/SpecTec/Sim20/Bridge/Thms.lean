module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Bridge

/-!
# The 2.0 whole-step bridge: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim20.Whole`; see `docs/projects/wasm-spec-bridge.md`.

* **`not_wholeStepBwd`**: `Sim20.Task.wholeStepBwd` (the backward half at any builtins, from a
  typed image) is false: `memory.grow-fail` fires without a memory at every builtins, where V2
  is stuck. No open whole-step `Task` of 2.0 remains; the backward half that holds is
  `wholeStepBwdW` (`GoodW`: defined conversions, no vector operator, named resources exist).
* **`wholeStepFwd20GP`** (`Task.wholeStepFwd20GP`): the nested forward half in the corrected
  script at `storeB` on `FwdStep20G` and V2's packed loads, joined by `FwdBase20.or`;
  `nest20_fwdGP_of_fwdL`: it contains `Task.wholeStepFwd20S`'s fragment.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Whole

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.not_wholeStepBwd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms not_wholeStepBwd

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepFwd20GP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wholeStepFwd20GP

end Silmaril.Wasm.SpecTec.Sim20.Whole
