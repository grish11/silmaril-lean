module

public import Silmaril.SSA.Isotope.LetIter.AbortSequence.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.AbortSequence

/-! # Equivalence and substitution for explicit empty elimination -/

public section

namespace Silmaril.Isotope.LetIter.LocallyNameless

universe u v w r

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ν : Type w} [DecidableEq ν] {Γ : Ctx ν τ}
  {n m : Nat} {β : BoundCtx τ n} {δ : BoundCtx τ m}
  {a b : Tm ν Φ n} {A : τ} {σ : Fin n → Tm ν Φ m}

/-- Every typed bound substitution preserves the new primitive equation. -/
theorem AbortSequence.bsubst (h : AbortSequence Γ β a b A) (s : TypedSubst (Γ := Γ) β δ σ) :
    AbortSequence Γ δ (Tm.bsubst σ a) (Tm.bsubst σ b) A := by
  cases h with
  | sequence ha => exact .sequence (ha.bsubst s)
  | unsequence ha => exact .unsequence (ha.bsubst s)

variable {ε : Type r} [HasEff Φ ε] {pe : ε}

/-- The extended theory sequences even an effectful empty scrutinee. -/
theorem AbortEquiv.sequence (ha : HasType Φ Γ β a Silmaril.empty) :
    AbortEquiv pe Γ β (.abort a) (.let₁ a (.abort (.bv 0))) A :=
  .primitive (.sequence ha) (.abort ha) (.let₁ ha (.abort .bv))

/-- The two orientations of the new equation make the compatible closure symmetric. -/
theorem AbortEquiv.symm (h : AbortEquiv pe Γ β a b A) : AbortEquiv pe Γ β b a A :=
  AbortEquiv.symm_proof h

/-- Pure typed substitutions preserve the full extension, including its exact equations. -/
theorem AbortEquiv.bsubst (h : AbortEquiv pe Γ β a b A) (s : PureTypedSubst pe Γ β δ σ) :
    AbortEquiv pe Γ δ (Tm.bsubst σ a) (Tm.bsubst σ b) A :=
  Refinement.bsubst (fun sub law => law.bsubst sub.typed) h s

end Silmaril.Isotope.LetIter.LocallyNameless
