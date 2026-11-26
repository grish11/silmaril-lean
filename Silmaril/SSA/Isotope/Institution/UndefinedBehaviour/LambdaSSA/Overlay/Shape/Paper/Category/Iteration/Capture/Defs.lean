module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Syntax.Iteration.Thms

/-! # A product input for a guarded native captured region -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Paper

open Silmaril.DeBruijn (lift)
open LambdaSSA.Region (ValueBranches)

universe u v

variable {Φ : Type u} {κ : Type v} [HasTy Φ (Ty κ)] {X A B : Ty κ}

/-- Unpack the capture and seed once, ahead of the original region. Slot
zero in the body is the seed and slot one is the capture. -/
def unpackCapture (r : LambdaSSA.Region Φ) : LambdaSSA.Region Φ :=
  .let₂ (.var 0) (r.renameVars (lift (lift Nat.succ)))

theorem unpackCapture_typed {r : LambdaSSA.Region Φ} (hr : ValueBranches [A, X] r [B]) :
    ValueBranches [.product X A] (unpackCapture r) [B] :=
  .let₂ (.var (i := 0) rfl) (hr.renameVars (((SSA.Ren.wk [] (.product X A)).lift X).lift A))

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Paper
