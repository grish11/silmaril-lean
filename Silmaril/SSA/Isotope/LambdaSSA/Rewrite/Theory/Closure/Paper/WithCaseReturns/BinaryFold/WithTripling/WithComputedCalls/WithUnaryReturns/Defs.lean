module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Defs

/-! # Unary forwarding over the computed-call quotient -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns

open CategoryTheory
open Paper.Extension.Singleton (homRel)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

/-- Add the singleton-return instance of the printed region
`let₁-let₁` rule. Both endpoints forward only the bound result.

[Printed rule](https://github.com/imbrem/thesis/blob/198c67fae4240edf1bc19194cda63adedb0944cd/papers/isotope/denotational-semantics-of-ssa.tex#L2025-L2029). -/
abbrev Step (Γ : VCtx τ) (r s : Region Φ) (L : LCtx τ) : Prop :=
  WithComputedCalls.Step pe Γ r s L ∨ Paper.UnaryReturn.Step Γ r s L

abbrev Eqv := Paper.Extension.Eqv (Step (τ := τ) (Φ := Φ) pe)

abbrev TypeCategory := Paper.Extension.Singleton.TypeCategory (Step (τ := τ) (Φ := Φ) pe)

/-- Include old computed-call derivations while keeping every exact type. -/
def fromWithComputedCalls :
    WithComputedCalls.TypeCategory (τ := τ) (Φ := Φ) pe ⥤ TypeCategory (τ := τ) (Φ := Φ) pe := by
  refine CategoryTheory.Quotient.lift (homRel (WithComputedCalls.Step pe))
    (Paper.Extension.Singleton.projection (Step pe)) ?_
  rintro _ _ _ _ ⟨r, s, hr, hs, hf, hg, eqv⟩
  exact CategoryTheory.Quotient.sound _ ⟨r, s, hr, hs, hf, hg, eqv.mapSeed Or.inl⟩

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns
