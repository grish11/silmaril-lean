module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Defs

/-! # A feedback step with a separate block for pending replies -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns

open Silmaril.Isotope.LambdaSSA
open CategoryTheory CategoryTheory.Limits

universe u v w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

variable {S R B : Extension.Singleton.TypeCategory (JoinedStep (τ := τ) (Φ := Φ) pe)}

/-- The original states issue the first request and enter the pending reply block.
The pending block runs the second step and exits with either a result or an
original state. The left-associated result presents the two recursive blocks. -/
noncomputable def requestBlocks (first : S ⟶ R) (second : R ⟶ B ⨿ S) :
    S ⨿ R ⟶ (B ⨿ S) ⨿ R :=
  coprod.desc (first ≫ coprod.inr) (second ≫ coprod.inl)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns
