module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.ComputedCall.Defs

/-! # WithTripling with returned computed calls -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls

open CategoryTheory
open Paper.Extension.Singleton (homRel)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

/-- Add the returned-call equation to the exact WithTripling seed. -/
abbrev Step (Γ : VCtx τ) (r s : Region Φ) (L : LCtx τ) : Prop :=
  WithTripling.Step pe Γ r s L ∨ Paper.WithComputedCallReturns.Step Γ r s L

abbrev Eqv := Paper.Extension.Eqv (Step (τ := τ) (Φ := Φ) pe)

abbrev TypeCategory := Paper.Extension.Singleton.TypeCategory (Step (τ := τ) (Φ := Φ) pe)

/-- The identity-on-types functor induced by inclusion of the old seed. -/
def fromWithTripling :
    WithTripling.TypeCategory (τ := τ) (Φ := Φ) pe ⥤ TypeCategory (τ := τ) (Φ := Φ) pe := by
  refine CategoryTheory.Quotient.lift (homRel (WithTripling.Step pe)) (Paper.Extension.Singleton.projection (Step pe)) ?_
  rintro _ _ _ _ ⟨r, s, hr, hs, hf, hg, eqv⟩
  exact CategoryTheory.Quotient.sound _ ⟨r, s, hr, hs, hf, hg, eqv.mapSeed Or.inl⟩

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls
