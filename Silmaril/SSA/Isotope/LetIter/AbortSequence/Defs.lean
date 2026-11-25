module

public import Silmaril.Raw.SSA.Isotope.LetIter.LocallyNameless.TheorySubstitution

/-! # LetIter with explicit sequencing of empty elimination -/

@[expose] public section

namespace Silmaril.Isotope.LetIter.LocallyNameless

universe u v w r

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ν : Type w} [DecidableEq ν]

/-- The two orientations of sequencing an empty-typed scrutinee before abort.
The scrutinee may have effects. -/
inductive AbortSequence (Γ : Ctx ν τ) : TypedRelation ν Φ τ where
  | sequence {n : Nat} {β : BoundCtx τ n} {a : Tm ν Φ n} {A : τ}
      (ha : HasType Φ Γ β a Silmaril.empty) :
      AbortSequence Γ β (.abort a) (.let₁ a (.abort (.bv 0))) A
  | unsequence {n : Nat} {β : BoundCtx τ n} {a : Tm ν Φ n} {A : τ}
      (ha : HasType Φ Γ β a Silmaril.empty) :
      AbortSequence Γ β (.let₁ a (.abort (.bv 0))) (.abort a) A

variable {ε : Type r} [HasEff Φ ε]

/-- The compatible closure of exact LetIter equivalence and explicit abort sequencing.
Typed uniformity from the exact theory is included through `Refinement.equiv`. -/
abbrev AbortEquiv (pe : ε) (Γ : Ctx ν τ) : TypedRelation ν Φ τ :=
  Refinement pe Γ (AbortSequence Γ)

end Silmaril.Isotope.LetIter.LocallyNameless
