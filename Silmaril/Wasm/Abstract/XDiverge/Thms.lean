module

public import Silmaril.Wasm.Abstract.XDiverge.Defs
public import Silmaril.Wasm.Abstract.XRecursion.Defs
import Silmaril.Proofs.Wasm.Abstract.XDiverge.Basic

/-!
# Coinductive divergence through every call form: theorems

* Unfolding and coinduction: `evalDivX_iff_step`, `localDivX_iff_step`,
  `evalDivX_of_coind`, `localDivX_of_coind`; local divergence is divergence
  (`localDivX_le_evalDivX`).
* **The direct part is `Interp`'s.** On a store whose functions have no
  extended call form (`XRecursion.StoreXFree`) and on direct code, extended
  divergence is `Interp.EvalDiv` (`evalDivX_iff_evalDiv`), local extended
  divergence is `Interp.LocalDiv` (`localDivX_iff_localDiv`), and so for calls
  (`funDivX_iff_funDiv`).

**Not yet.** Answers exclude divergence (determinism of the closed extended
semantics), the decomposition into finite descents to a locally diverging call
or an infinite chain, and Core 3.0 adequacy (pending the checker extension
parameter).
-/

public section

namespace Silmaril.Wasm.Abstract.XDiverge

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Interp (Problem EvalDiv LocalDiv FunDiv)
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.XRecursion

variable {H : Type}

theorem evalDivX_iff_step {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr} :
    EvalDivX s f stk es ↔ DivStepX EvalDivX EvalDivX s f stk es :=
  Silmaril.Proofs.Wasm.Abstract.XDiverge.evalDivX_unfold

theorem localDivX_iff_step {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr} :
    LocalDivX s f stk es ↔ DivStepX LocalDivX ⊥ s f stk es :=
  Silmaril.Proofs.Wasm.Abstract.XDiverge.localDivX_unfold

theorem evalDivX_of_coind {X : Problem H}
    (h : ∀ s f stk es, X s f stk es → DivStepX X X s f stk es) : X ≤ EvalDivX :=
  Silmaril.Proofs.Wasm.Abstract.XDiverge.evalDivX_coind h

theorem localDivX_of_coind {X : Problem H}
    (h : ∀ s f stk es, X s f stk es → DivStepX X ⊥ s f stk es) : X ≤ LocalDivX :=
  Silmaril.Proofs.Wasm.Abstract.XDiverge.localDivX_coind h

theorem localDivX_le_evalDivX : (LocalDivX : Problem H) ≤ EvalDivX :=
  Silmaril.Proofs.Wasm.Abstract.XDiverge.localDivX_le_evalDivX

/-- **On direct stores and code, extended divergence is `Interp.EvalDiv`.** -/
theorem evalDivX_iff_evalDiv {s : Store H} (hs : StoreXFree s) {f : Frame} {stk : List Val}
    {es : List BExpr} (hx : xFreeL es = true) : EvalDivX s f stk es ↔ EvalDiv s f stk es :=
  ⟨Silmaril.Proofs.Wasm.Abstract.XDiverge.evalDiv_of_evalDivX hs hx,
    Silmaril.Proofs.Wasm.Abstract.XDiverge.evalDivX_of_evalDiv hs hx⟩

/-- **On direct stores and code, local extended divergence is `Interp.LocalDiv`.** -/
theorem localDivX_iff_localDiv {s : Store H} (hs : StoreXFree s) {f : Frame} {stk : List Val}
    {es : List BExpr} (hx : xFreeL es = true) : LocalDivX s f stk es ↔ LocalDiv s f stk es :=
  ⟨Silmaril.Proofs.Wasm.Abstract.XDiverge.localDiv_of_localDivX hs hx,
    Silmaril.Proofs.Wasm.Abstract.XDiverge.localDivX_of_localDiv hs hx⟩

theorem funDivX_iff_funDiv {s : Store H} (hs : StoreXFree s) (a : Nat) (vs : List Val) :
    FunDivX s a vs ↔ FunDiv s a vs := by
  constructor
  · rintro ⟨fi, fn, hfi, hc, h⟩
    exact ⟨fi, fn, hfi, hc, (evalDivX_iff_evalDiv hs (hs a fi fn hfi hc)).1 h⟩
  · rintro ⟨fi, fn, hfi, hc, h⟩
    exact ⟨fi, fn, hfi, hc, (evalDivX_iff_evalDiv hs (hs a fi fn hfi hc)).2 h⟩

end Silmaril.Wasm.Abstract.XDiverge
