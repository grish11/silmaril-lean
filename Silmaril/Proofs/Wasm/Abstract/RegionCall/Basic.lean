module

public import Silmaril.Wasm.Abstract.Recursion.Thms
public import Silmaril.Wasm.Cfg.Region.Defs
public import Silmaril.Wasm.Abstract.RegionCall.Defs

/-!
# The closed oracle, restricted to checked invocations, is `Region.CallSound` (proofs)
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.RegionCall

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract

variable {H : Type}

theorem callSound_closedCallOk (P : Numerics.Profile) (host : HostSemantics H) :
    Cfg.Region.CallSound P host (closedCallOk (H := H)) := by
  intro s s₁ f a fi ps rs us fl hfi hty _ ⟨hC, hS, hok⟩
  rw [closedCall_eq] at hC
  obtain ⟨fi', fn, ps', rs', f₂, hfi', hcode, hty', hev⟩ := hC
  obtain rfl : fi = fi' := Option.some.inj (hfi.symm.trans hfi')
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hty.symm.trans hty'))
  obtain ⟨h₁, h₂, h₃⟩ := Silmaril.Wasm.Interp.steps_callRef_of_eval (P := P) (host := host)
    hS hok hfi hcode hty hev f
  exact ⟨h₁, h₂, fun t ht => (h₃ t ht).elim⟩

end Silmaril.Proofs.Wasm.Abstract.RegionCall
