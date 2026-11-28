module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.BinaryLet.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProductDestructureReturns.Defs

/-! # Opt-in guarded singleton product producers -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers

open Silmaril Silmaril.Isotope.LambdaSSA
open Paper.SingletonReification.BinaryLet (returnPair returnPair_typed)
open Paper.RetainedLet (returnOnce returnOnce_typed)

universe u v w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Identify two guarded ways of evaluating and returning a product once at a
singleton interface. -/
inductive Step : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop where
  | producer {X A B : τ} {a : Tm Φ} (ha : Tm.HasType [X] a (product A B)) :
      Step [X] (returnPair a) (returnOnce a) [product A B]

/-- Each producer representative already has constructor-valued branch arguments. -/
theorem Step.valueBranches {Γ L : List τ} {r s : Region Φ} (step : Step Γ r s L) :
    ValueBranches Γ r L ∧ ValueBranches Γ s L := by
  cases step with
  | producer ha => exact ⟨returnPair_typed ha, returnOnce_typed ha⟩

variable {ε : Type w} [HasEff Φ ε] (pe : ε)

/-- Opt in to only the singleton producer equation on top of the product-destructure join. -/
abbrev JoinedStep (Γ : VCtx τ) (r s : Region Φ) (L : LCtx τ) : Prop :=
  WithProductDestructureReturns.JoinedStep pe Γ r s L ∨ Step Γ r s L

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers
