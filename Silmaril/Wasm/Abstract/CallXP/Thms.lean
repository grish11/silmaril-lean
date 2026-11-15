module

public import Silmaril.Wasm.Abstract.CallXP.Defs
import Silmaril.Proofs.Wasm.Abstract.CallXP.Basic

/-!
# Pending tail calls: theorems

* `EvalOXP.mono`, `FrameP.mono`: monotone in the oracle.
* **Legacy coincidence** on code without the extended call forms (`CallX.xFreeL`): an `EvalOXP`
  run never ends in a pending tail call (`evalOXP_not_tail`), and its flow runs are exactly
  `CallXE.EvalOXE`'s (`evalOXP_iff_evalOXE`). So the existing exception theorems
  (`Interp.EHSim`, `Interp.EHClose`), all stated for such code, are unchanged by the pending
  semantics; it only differs where `EvalOXE` is not faithful (a tail call inside a handler).
-/

public section

namespace Silmaril.Wasm.Abstract.CallXP

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract (CallRel)
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXE

variable {H : Type}

theorem EvalOXP.mono {C C' : CallRel H} (hC : C ≤ C') {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} {r : Store H × Frame × POut} (h : EvalOXP C s f stk es r) :
    EvalOXP C' s f stk es r :=
  Silmaril.Proofs.Wasm.Abstract.CallXP.mono hC h

theorem FrameP.mono {C C' : CallRel H} (hC : C ≤ C') {x : Store H × POut} {y : Store H × Flow}
    (h : FrameP C x y) : FrameP C' x y :=
  Silmaril.Proofs.Wasm.Abstract.CallXP.frameP_mono hC h

/-- On code without the extended call forms no tail call is pending. -/
theorem evalOXP_not_tail {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} {s' : Store H} {f' : Frame} {a n : Nat} {args : List Val}
    (hx : xFreeL es = true) : ¬ EvalOXP C s f stk es (s', f', .tail a args n) := fun h => by
  obtain ⟨_, h1, -⟩ := Silmaril.Proofs.Wasm.Abstract.CallXP.to_evalOXE h hx
  cases h1

/-- **Legacy coincidence**: on code without the extended call forms, `EvalOXP` is `EvalOXE`. -/
theorem evalOXP_iff_evalOXE {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} {s' : Store H} {f' : Frame} {fl : Flow} (hx : xFreeL es = true) :
    EvalOXP C s f stk es (s', f', .flow fl) ↔ EvalOXE C s f stk es (s', f', fl) := by
  constructor
  · intro h
    obtain ⟨fl', h1, d⟩ := Silmaril.Proofs.Wasm.Abstract.CallXP.to_evalOXE h hx
    cases h1; exact d
  · exact fun h => Silmaril.Proofs.Wasm.Abstract.CallXP.of_evalOXE h hx

end Silmaril.Wasm.Abstract.CallXP
