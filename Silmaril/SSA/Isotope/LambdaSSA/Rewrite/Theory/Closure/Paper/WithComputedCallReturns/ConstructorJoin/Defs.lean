module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedCallReturns.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.Joined.Defs

/-! # Computed calls in the opt-in constructor join -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedCallReturns.ConstructorJoin

universe u v w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {ε : Type w} [HasEff Φ ε]

abbrev Seed (pe : ε) (Γ : VCtx τ) (r s : Region Φ) (L : LCtx τ) : Prop :=
  WithConstructorSequencing.Joined.Seed pe Γ r s L ∨ WithComputedCallReturns.Step Γ r s L

abbrev Eqv (pe : ε) := Extension.Eqv (Seed (τ := τ) (Φ := Φ) pe)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedCallReturns.ConstructorJoin
