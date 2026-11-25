module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Thms
public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Continuation

/-! # Constructor values and typing of let and CFG equations -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open Silmaril.Isotope.LambdaSSA

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

omit [HasTy Φ τ] in
theorem branchValue_subst {Γ Δ : VCtx τ} {b : Tm Φ} {B : τ} (h : Tm.BranchValue Δ b B)
    {σ : Nat → Tm Φ}
    (hσ : ∀ ⦃i A⦄, At Δ i A → Tm.BranchValue Γ (σ i) A) :
    Tm.BranchValue Γ (b.subst σ) B := by
  induction h with
  | var hi => exact hσ hi
  | unit => exact .unit
  | pair _ _ iha ihb => exact .pair iha ihb
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih

omit [HasTy Φ τ] in
theorem branchValue_singleSubst {Γ : VCtx τ} {a b : Tm Φ} {A B : τ}
    (ha : Tm.BranchValue Γ a A) (hb : Tm.BranchValue (A :: Γ) b B) :
    Tm.BranchValue Γ (b.subst (Tm.singleSubst a)) B := by
  apply branchValue_subst hb
  intro i C hi
  cases i with
  | zero =>
      have h : A = C := Option.some.inj hi
      cases h
      exact ha
  | succ i => exact .var hi

theorem rewriteEquiv_typed {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : Region.RewriteEquiv Γ r s L) : Region.HasType Γ r L ∧ Region.HasType Γ s L := by
  induction h with
  | entry h => exact h.typed
  | symm _ ih => exact ⟨ih.2, ih.1⟩
  | trans _ _ ih ih' => exact ⟨ih.1, ih'.2⟩
  | let₁ ha _ ih => exact ⟨.let₁ ha ih.1, .let₁ ha ih.2⟩
  | let₂ ha _ ih => exact ⟨.let₂ ha ih.1, .let₂ ha ih.2⟩
  | case ha _ _ ihl ihr => exact ⟨.case ha ihl.1 ihr.1, .case ha ihl.2 ihr.2⟩
  | cfg R _ _ ihe ihb =>
      exact ⟨.cfg R ihe.1 (fun i => (ihb i).1), .cfg R ihe.2 (fun i => (ihb i).2)⟩
  | letBr ha hb hl => exact ⟨.let₁ ha.hasType (.br hl hb.hasType),
      .br hl (branchValue_singleSubst ha hb).hasType⟩
  | caseInl ha hl hr => exact ⟨.case (.inl ha) hl hr, .let₁ ha hl⟩
  | caseInr hb hl hr => exact ⟨.case (.inr hb) hl hr, .let₁ hb hr⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
