module

public import Silmaril.Sim.Wasm.Defs
public import Silmaril.Wasm.Verify.FnSpec.Defs

/-!
# Wasm simulators: per-method soundness from `Verify.FnSpec` (header)

The adapter from the store-level function specifications of `Silmaril.Wasm.Verify.FnSpec` (proved
with the `wasm_vc` tactic) to the bridge interface `Silmaril.Sim.Wasm.ExportSim`:

* `ExportSim.methodFnSpec K B R c`: the per-method soundness problem of command `c` as an
  `FnSpec` (`H = Nat`), with the reference state as the ghost input;
* `ExportSim.methodOK_of_vc` (`Thms`): its verification condition gives `MethodOK`.
-/

@[expose] public section

namespace Silmaril.Sim.Wasm.ExportSim

open Silmaril.Wasm.Execution.Core

variable {C L V : Type}

/-- The `wasm_vc` form of the method specification (`H = Nat`): input = ghost reference
state. -/
def methodFnSpec (K : ExportSim C L V Nat) (B : Machine C L V) (R : Store Nat → B.St → Prop)
    (c : C) (nresults : Nat := 1) : Silmaril.Wasm.Verify.FnSpec B.St where
  args _ := K.args c
  nresults := nresults
  pre b _ s := R s b
  post b _ _ res s' := K.ok c res → ∃ b', B.step c b b' ∧ R s' b'

end Silmaril.Sim.Wasm.ExportSim

end
