module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Labels

/-! # Formation of CFG rewrite endpoints -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open Silmaril.Isotope.LambdaSSA

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

theorem branchValue_hasType {Γ : VCtx τ} {a : Tm Φ} {A : τ}
    (h : Tm.BranchValue Γ a A) : Tm.HasType Γ a A := by
  induction h with
  | var hi => exact .var hi
  | unit => exact .unit
  | pair _ _ iha ihb => exact .pair iha ihb
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih

theorem cfgEquiv_typed {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : Region.CfgEquiv Γ r s L) : Region.HasType Γ r L ∧ Region.HasType Γ s L := by
  induction h with
  | refl ht => exact ⟨ht, ht⟩
  | symm _ ih => exact ⟨ih.2, ih.1⟩
  | trans _ _ ih ih' => exact ⟨ih.1, ih'.2⟩
  | let₁ ha _ ih => exact ⟨.let₁ ha ih.1, .let₁ ha ih.2⟩
  | let₂ ha _ ih => exact ⟨.let₂ ha ih.1, .let₂ ha ih.2⟩
  | case ha _ _ ihl ihr => exact ⟨.case ha ihl.1 ihr.1, .case ha ihl.2 ihr.2⟩
  | cfg R _ _ ihe ihb =>
      exact ⟨.cfg R ihe.1 (fun i => (ihb i).1), .cfg R ihe.2 (fun i => (ihb i).2)⟩
  | cfgZero he _ =>
      exact ⟨.cfg Fin.elim0 he (fun i => i.elim0), he⟩
  | cfgBrExit R hl ha hb =>
      exact ⟨.cfg R (.br (exitAt R hl) (branchValue_hasType ha)) hb, .br hl (branchValue_hasType ha)⟩
  | cfgBrLocal R i ha hb =>
      exact ⟨.cfg R (.br (localAt R i _) (branchValue_hasType ha)) hb,
        .cfg R (.let₁ (branchValue_hasType ha) (hb i)) hb⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
