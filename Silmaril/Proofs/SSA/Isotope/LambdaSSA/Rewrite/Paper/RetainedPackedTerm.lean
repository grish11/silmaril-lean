module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedLet.Generation.PackedTerm.Defs

/-! # Exact typing for the opened packed term -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RetainedPackedTerm

open Silmaril Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region.Paper.PackedBody (applyPackedTerm)

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {X A D : τ}

theorem applyPackedTerm_typed {t : Tm Φ} (ht : Tm.HasType [product X A] t D) :
    Tm.HasType [A, X] (applyPackedTerm t) D := by
  apply Tm.HasType.subst _ ht
  intro i B hi
  cases i with
  | zero =>
    cases Option.some.inj hi
    exact .pair (.var (i := 1) rfl) (.var (i := 0) rfl)
  | succ i => simp [At] at hi

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RetainedPackedTerm
