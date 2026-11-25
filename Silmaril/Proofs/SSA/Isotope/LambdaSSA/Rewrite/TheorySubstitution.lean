module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Thms
import Silmaril.Raw.SSA.Isotope.LambdaSSA.ContinuationLaws
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.TheoryTyping

/-! # Substitution of constructor values in typed λSSA rewrites -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open Silmaril.Isotope.LambdaSSA

variable {τ : Type u} [TypeFormers τ] {Φ : Type v}

theorem branchValue_rename {Γ Δ : VCtx τ} {a : Tm Φ} {A : τ}
    (ha : Tm.BranchValue Γ a A) {ρ : Nat → Nat} (hρ : Silmaril.Isotope.SSA.Ren Γ Δ ρ) :
    Tm.BranchValue Δ (a.rename ρ) A := by
  induction ha with
  | var hi => exact .var (hρ hi)
  | unit => exact .unit
  | pair _ _ iha ihb => exact .pair iha ihb
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih

theorem liftValues {Γ Δ : VCtx τ} {σ : Nat → Tm Φ}
    (hσ : ∀ ⦃i A⦄, At Γ i A → Tm.BranchValue Δ (σ i) A) (B : τ) :
    ∀ ⦃i A⦄, At (B :: Γ) i A → Tm.BranchValue (B :: Δ) (Tm.liftSubst σ i) A := by
  intro i A hi
  cases i with
  | zero =>
      cases Option.some.inj hi
      exact .var rfl
  | succ i => exact branchValue_rename (hσ hi) (Silmaril.Isotope.SSA.Ren.wk Δ B)

variable [HasTy Φ τ]

theorem valuesTyped {Γ Δ : VCtx τ} {σ : Nat → Tm Φ}
    (hσ : ∀ ⦃i A⦄, At Γ i A → Tm.BranchValue Δ (σ i) A) :
    Tm.Subst.HasType Γ Δ σ :=
  fun _ _ hi => (hσ hi).hasType

private theorem cfgEquiv_substVars {Γ Δ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : Region.CfgEquiv Γ r s L) {σ : Nat → Tm Φ}
    (hσ : ∀ ⦃i A⦄, At Γ i A → Tm.BranchValue Δ (σ i) A) :
    Region.CfgEquiv Δ (r.substVars σ) (s.substVars σ) L := by
  induction h generalizing Δ σ with
  | refl hr => exact .refl (hr.substVars (valuesTyped hσ))
  | symm _ ih => exact .symm (ih hσ)
  | trans _ _ ihr ihs => exact .trans (ihr hσ) (ihs hσ)
  | let₁ ha _ ih => exact .let₁ (ha.subst (valuesTyped hσ)) (ih (liftValues hσ _))
  | let₂ ha _ ih => exact .let₂ (ha.subst (valuesTyped hσ)) (ih (liftValues (liftValues hσ _) _))
  | case ha _ _ ihl ihr =>
      exact .case (ha.subst (valuesTyped hσ)) (ihl (liftValues hσ _)) (ihr (liftValues hσ _))
  | cfg R _ _ ihe ihb => exact .cfg R (ihe hσ) (fun i => ihb i (liftValues hσ _))
  | cfgZero he _ => exact .cfgZero (he.substVars (valuesTyped hσ)) _
  | cfgBrExit R hℓ ha hb =>
      exact .cfgBrExit R hℓ (branchValue_subst ha hσ)
        (fun i => (hb i).substVars (valuesTyped (liftValues hσ _)))
  | cfgBrLocal R i ha hb =>
      exact .cfgBrLocal R i (branchValue_subst ha hσ)
        (fun j => (hb j).substVars (valuesTyped (liftValues hσ _)))

theorem rewriteEquiv_substVars {Γ Δ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : Region.RewriteEquiv Γ r s L) {σ : Nat → Tm Φ}
    (hσ : ∀ ⦃i A⦄, At Γ i A → Tm.BranchValue Δ (σ i) A) :
    Region.RewriteEquiv Δ (r.substVars σ) (s.substVars σ) L := by
  induction h generalizing Δ σ with
  | entry h => exact .entry (cfgEquiv_substVars h hσ)
  | symm _ ih => exact .symm (ih hσ)
  | trans _ _ ihr ihs => exact .trans (ihr hσ) (ihs hσ)
  | let₁ ha _ ih => exact .let₁ (ha.subst (valuesTyped hσ)) (ih (liftValues hσ _))
  | let₂ ha _ ih => exact .let₂ (ha.subst (valuesTyped hσ)) (ih (liftValues (liftValues hσ _) _))
  | case ha _ _ ihl ihr =>
      exact .case (ha.subst (valuesTyped hσ)) (ihl (liftValues hσ _)) (ihr (liftValues hσ _))
  | cfg R _ _ ihe ihb => exact .cfg R (ihe hσ) (fun i => ihb i (liftValues hσ _))
  | @letBr _ a A b B _ ℓ ha hb hℓ =>
      change Region.RewriteEquiv _
        (.let₁ (a.subst σ) (.br ℓ (b.subst (Tm.liftSubst σ))))
        (.br ℓ ((b.subst (Tm.singleSubst a)).subst σ)) _
      rw [Tm.subst_comp b (Tm.singleSubst a), Tm.singleSubst_comp, ← Tm.subst_comp]
      exact .letBr (branchValue_subst ha hσ) (branchValue_subst hb (liftValues hσ _)) hℓ
  | caseInl ha hl hr =>
      exact .caseInl (ha.subst (valuesTyped hσ))
        (hl.substVars (valuesTyped (liftValues hσ _))) (hr.substVars (valuesTyped (liftValues hσ _)))
  | caseInr hb hl hr =>
      exact .caseInr (hb.subst (valuesTyped hσ))
        (hl.substVars (valuesTyped (liftValues hσ _))) (hr.substVars (valuesTyped (liftValues hσ _)))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
