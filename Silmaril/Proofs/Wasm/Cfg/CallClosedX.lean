module

public import Silmaril.Wasm.Cfg.MachineClosedX.Defs
public import Silmaril.Wasm.Cfg.Region.Defs

@[expose] public section

/-!
# The typed closed extended oracle is Core-sound for every `call_ref` form

From `Interp.OracleX.oracleSoundT_typedClosed` (no host): every answer of `closedXOk` is a Core
run of the call in any caller frame and with any `call_ref` annotation, to its values or its
trap. It never throws: the answer's flow satisfies `Interp.FlowOk`, which excludes exceptions.
-/

namespace Silmaril.Wasm.Cfg.Proofs.Region

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Region Silmaril.Wasm.Execution.Core

variable {H : Type}

theorem callSoundA_closedXOk (P : Numerics.Profile) :
    CallSoundA P Interp.noHostX (Machine.closedXOk (H := H)) := by
  intro s s₁ f a fi ps rs us fl c hc hfi hty hn hcall
  obtain ⟨hS, hcx⟩ := hcall
  obtain ⟨⟨ob, -, hflow, -⟩, hv, ht⟩ :=
    Interp.OracleX.oracleSoundT_typedClosed (P := P) s s₁ f a fi ps rs us fl c hS hfi hty hn hc hcx
  refine ⟨hv, ht, fun t he => ?_⟩
  subst he
  exact hflow.elim

end Silmaril.Wasm.Cfg.Proofs.Region
