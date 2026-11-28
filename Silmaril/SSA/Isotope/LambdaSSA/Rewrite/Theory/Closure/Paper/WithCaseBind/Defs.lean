module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedCase.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Defs

/-! # Opt-in binding of a computed case discriminator -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind

open Silmaril
open RetainedCase (boundCase boundCase_typed)

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Evaluate the same discriminator once, keep the original environment,
and select the arm from the bound sum. -/
inductive Step : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop where
  | bind {Γ : VCtx τ} {L : LCtx τ} {A B : τ} {a : Tm Φ} {l r : Region Φ}
      (ha : Tm.HasType Γ a (coprod A B)) (hl : ValueBranches (A :: Γ) l L)
      (hr : ValueBranches (B :: Γ) r L) :
      Step Γ (.case a l r) (.let₁ a (boundCase l r)) L

theorem Step.valueBranches {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ} (e : Step Γ r s L) :
    ValueBranches Γ r L ∧ ValueBranches Γ s L := by
  cases e with
  | bind ha hl hr => exact ⟨.case ha hl hr, .let₁ ha (boundCase_typed hl hr)⟩

/-- Add the discriminator conversion to an explicitly chosen contextual seed. -/
abbrev JoinedStep (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
    (Γ : VCtx τ) (r s : Region Φ) (L : LCtx τ) : Prop :=
  Seed Γ r s L ∨ Step Γ r s L

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind
