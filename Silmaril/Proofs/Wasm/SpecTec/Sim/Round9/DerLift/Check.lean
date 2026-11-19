module

public import Silmaril.Wasm.SpecTec.Sim.Round9.DerLift.Defs

/-!
# Round 9, REH: the rule families of the backward lift (kernel checks)

* `liftSimpleIdx_fixed`: the `Step_read` rules of the fixed script that pass `liftSimple` are
  exactly `liftSimpleRules` (74 of 103).
* `liftSimpleIs_fixed`: each of them does, read at its index.
* `liftNxIdx_fixed`, `liftNxIs_fixed`: the same for `liftNx` at `Step_pure` (66 of 79);
  `liftNxIdx_step_fixed`: no rule of `Step` or `Step_read` passes `liftNx`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.DerLift

open Silmaril.SpecTec.Sem

set_option maxRecDepth 100000 in
/-- **The rules of `Step_read` that pass `liftSimple`.** -/
theorem liftSimpleIdx_fixed :
    liftSimpleIdx (relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed) = liftSimpleRules := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **Each rule of `liftSimpleRules` passes `liftSimple`.** -/
theorem liftSimpleIs_fixed :
    liftSimpleIs (relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed) liftSimpleRules = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **The rules of `Step_pure` that pass `liftNx`.** -/
theorem liftNxIdx_fixed :
    liftNxIdx (relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed) "Step_pure" = liftNxRules := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **No rule of `Step` or `Step_read` passes `liftNx`.** -/
theorem liftNxIdx_step_fixed :
    liftNxIdx (relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed) "Step" = [] ∧
      liftNxIdx (relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed) "Step_read" = [] := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **Each rule of `liftNxRules` passes `liftNx`.** -/
theorem liftNxIs_fixed :
    liftNxIs (relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed) "Step_pure" liftNxRules =
      true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round9.DerLift
