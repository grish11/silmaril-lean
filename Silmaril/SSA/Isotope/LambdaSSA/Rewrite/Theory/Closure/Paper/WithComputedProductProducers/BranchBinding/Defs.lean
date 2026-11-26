module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.Defs

/-! # The literal raw product producer -/

public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.BranchBinding

open Silmaril.Isotope.LambdaSSA
open Paper.SingletonReification.BinaryLet (returnPair)
open Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding (AddBinding)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Destructure and rebuild, or branch directly on the same typed scrutinee. -/
inductive RawStep : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop where
  | producer {X A B : τ} {a : Tm Φ} (ha : Tm.HasType [X] a (product A B)) :
      RawStep [X] (returnPair a) (.br 0 a) [product A B]

variable {ε : Type w} [HasEff Φ ε] (pe : ε)

/-- Add the literal producer and ordinary branch binding to the older raw theory. -/
abbrev RawJoinedStep (Γ : VCtx τ) (r s : Region Φ) (L : LCtx τ) : Prop :=
  AddBinding (fun Γ r s L =>
    WithProductDestructureReturns.JoinedStep pe Γ r s L ∨ RawStep Γ r s L) Γ r s L

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.BranchBinding
