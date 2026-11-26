module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedCallReturns.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Values.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProductDestructureReturns.Term.Defs

/-! # Opt-in returns of a product-input destructure -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProductDestructureReturns

open Silmaril Silmaril.Isotope.LambdaSSA
open CfgEta.TypeCategory (returnRegion returnRegion_typed)
open Paper.RetainedLet (unpackBody unpackBody_typed unpackTerm unpackTerm_typed)

universe u v w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Move destructuring of the sole product variable inside a singleton return. -/
inductive Step : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop where
  | unpack {X A D : τ} {b : Tm Φ} (hb : Tm.HasType [A, X] b D) :
      Step [product X A] (unpackBody (returnRegion b)) (returnRegion (unpackTerm b)) [D]

/-- Both representatives already have constructor-valued branch arguments. -/
theorem Step.valueBranches {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ} (h : Step Γ r s L) :
    ValueBranches Γ r L ∧ ValueBranches Γ s L := by
  cases h with
  | unpack hb => exact ⟨unpackBody_typed (returnRegion_typed hb), returnRegion_typed (unpackTerm_typed hb)⟩

variable {ε : Type w} [HasEff Φ ε]

/-- Adjoin only the product-variable return equation to the computed-call join. -/
abbrev JoinedStep (pe : ε) (Γ : VCtx τ) (r s : Region Φ) (L : LCtx τ) : Prop :=
  WithComputedCallReturns.JoinedStep pe Γ r s L ∨ Step Γ r s L

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProductDestructureReturns
