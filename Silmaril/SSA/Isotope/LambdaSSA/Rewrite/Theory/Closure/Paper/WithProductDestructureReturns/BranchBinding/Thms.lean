module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProductDestructureReturns.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.ReturnSeeds.Thms

/-! # Branch binding is conservative for the product-return join -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProductDestructureReturns

open Silmaril Silmaril.Isotope.LambdaSSA
open Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding
  (AddBinding pairJoined_valueBranches guarded_eqv_iff_of_guardedSeed)

universe u v w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] {pe : ε} {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ}

/-- The computed-call join already meets the guarded-seed criterion. -/
theorem computedJoin_valueBranches (h : WithComputedCallReturns.JoinedStep pe Γ r s L) :
    ValueBranches Γ r L ∧ ValueBranches Γ s L :=
  h.elim pairJoined_valueBranches WithComputedCallReturns.Step.valueBranches

/-- Every generator of the enlarged join already has guarded endpoints. -/
theorem joined_valueBranches (h : JoinedStep pe Γ r s L) :
    ValueBranches Γ r L ∧ ValueBranches Γ s L :=
  h.elim computedJoin_valueBranches Step.valueBranches

/-- Adjoining raw branch binding preserves equality on guarded representatives. -/
theorem joined_guarded_eqv_iff (hr : ValueBranches Γ r L) (hs : ValueBranches Γ s L) :
    Extension.Eqv (AddBinding (JoinedStep pe)) Γ r s L ↔ Extension.Eqv (JoinedStep pe) Γ r s L :=
  guarded_eqv_iff_of_guardedSeed joined_valueBranches hr hs

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProductDestructureReturns
