module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedLet.Defs

/-! # A product-input destructure in expression syntax -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedLet

open Silmaril.Isotope.LambdaSSA
open Silmaril.DeBruijn (lift)

universe u v

variable {Φ : Type v}

/-- Decode both fields of the sole packed input inside a returned term. -/
def unpackTerm (b : Tm Φ) : Tm Φ :=
  .let₂ (.var 0) (b.rename (lift (lift Nat.succ)))

variable {τ : Type u} [TypeFormers τ] [HasTy Φ τ] {X A B : τ}

theorem unpackTerm_typed {b : Tm Φ} (hb : Tm.HasType [A, X] b B) :
    Tm.HasType [Silmaril.product X A] (unpackTerm b) B :=
  .let₂ (.var (i := 0) rfl)
    (hb.rename (((Ren.wk ([] : VCtx τ) (Silmaril.product X A)).lift X).lift A))

end Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedLet
