module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseAndUnaryReturns.Defs

/-! # The opt-in join of constructor sequencing and the four return rules -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.Joined

universe u v w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε]

/-- Add the three constructor sequencing steps to the existing joined seed.
Unary return fusion is already included in the joined seed. -/
abbrev Seed (pe : ε) (Γ : VCtx τ) (r s : Region Φ) (L : LCtx τ) : Prop :=
  WithCaseAndUnaryReturns.JoinedStep pe Γ r s L ∨ WithConstructorSequencing.Step Γ r s L

abbrev Eqv (pe : ε) := Extension.Eqv (Seed (τ := τ) (Φ := Φ) pe)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.Joined
