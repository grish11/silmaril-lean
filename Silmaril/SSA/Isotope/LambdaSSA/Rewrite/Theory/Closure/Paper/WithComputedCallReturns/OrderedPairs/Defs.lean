module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedCallReturns.ConstructorJoin.Defs

/-! # Ordered pair returns in the opt-in computed-call closure -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedCallReturns.OrderedPairs

universe u v w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {ε : Type w} [HasEff Φ ε]

abbrev Seed (pe : ε) (Γ : VCtx τ) (r s : Region Φ) (L : LCtx τ) : Prop :=
  ConstructorJoin.Seed pe Γ r s L ∨ WithPairReturns.Step Γ r s L

abbrev Eqv (pe : ε) := Extension.Eqv (Seed (τ := τ) (Φ := Φ) pe)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedCallReturns.OrderedPairs
