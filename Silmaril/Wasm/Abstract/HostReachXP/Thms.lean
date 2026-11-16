module

public import Silmaril.Wasm.Abstract.HostReachXP.Defs
public import Silmaril.Games.Abstract.CloseReach.Thms
import Silmaril.Proofs.Wasm.Abstract.HostReachXP.Basic

/-!
# The canonical closure with reach: theorems

* `wasmHOpenXP_reach`: every reach of a Wasm body is a prefix of a behaviour of `wasmHOpenXP`
  (its cut at the reached call);
* `closeR_wasmHOpenXP`, `wasmEvFunXP_eq_closeR`: **the canonical closure is the closure with
  reach**. A callee's trap at a call the body reaches is seen by `wasmEvFunXP` whether or not the
  body can finish after the call, with the log of the resolved prefix and of the actual callee.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- Every reach is a prefix of a behaviour of the canonical open module. -/
theorem wasmHOpenXP_reach (x : (wasmHShape H).self.Op) (u : List (HCall H))
    (z : (wasmHShape H).self.Op) (h : reachXP x u z) :
    ∃ w ∈ wasmHOpenXP x.1 x.2.2 x.2.1, ∃ ans rest, w.1 = u ++ ⟨.inr z, ans⟩ :: rest :=
  Silmaril.Proofs.Wasm.Abstract.HostReachXP.reachXP_syn x u z h

/-- **Closing with reach is closing** for the canonical open module. -/
theorem closeR_wasmHOpenXP :
    Shape.closeR (wasmHOpenXP (H := H)) reachXP = Shape.close wasmHOpenXP :=
  Silmaril.Proofs.Wasm.Abstract.HostReachXP.closeR_eq

/-- **The canonical closure with host calls is the closure with reach.** -/
theorem wasmEvFunXP_eq_closeR (s : Store H) (p : Nat × List Val) :
    wasmEvFunXP s p = Shape.closeR wasmHOpenXP reachXP p.1 s p.2 := by
  rw [closeR_wasmHOpenXP]; rfl

end Silmaril.Wasm.Abstract
