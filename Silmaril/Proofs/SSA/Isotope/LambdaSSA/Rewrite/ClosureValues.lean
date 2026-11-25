module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.TheorySubstitution
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.TheoryTyping
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Closure

/-! # Replacing values and continuations in the enlarged typed theory -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

theorem substitutionEquiv_substVars {Γ Δ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : SubstitutionEquiv Γ r s L) {σ : Nat → Tm Φ}
    (hσ : ∀ ⦃i A⦄, At Γ i A → Tm.BranchValue Δ (σ i) A) :
    SubstitutionEquiv Δ (r.substVars σ) (s.substVars σ) L := by
  induction h generalizing Δ σ with
  | base h => exact .base (h.substVars hσ)
  | symm _ ih => exact .symm (ih hσ)
  | trans _ _ ihr ihs => exact .trans (ihr hσ) (ihs hσ)
  | let₁ ha _ ih => exact .let₁ (ha.subst (valuesTyped hσ)) (ih (liftValues hσ _))
  | let₂ ha _ ih => exact .let₂ (ha.subst (valuesTyped hσ)) (ih (liftValues (liftValues hσ _) _))
  | case ha _ _ ihl ihr =>
      exact .case (ha.subst (valuesTyped hσ)) (ihl (liftValues hσ _)) (ihr (liftValues hσ _))
  | cfg R _ _ ihe ihb => exact .cfg R (ihe hσ) (fun i => ihb i (liftValues hσ _))
  | @letValue Γ a A r L ha hr =>
      change SubstitutionEquiv Δ
        (.let₁ (a.subst σ) (r.substVars (Tm.liftSubst σ)))
        ((r.substVars (Tm.singleSubst a)).substVars σ) L
      rw [substVars_comp r (Tm.singleSubst a), Tm.singleSubst_comp, ← substVars_comp]
      exact .letValue (branchValue_subst ha hσ) (hr.substVars (valuesTyped (liftValues hσ _)))
  | cfgOutward R hr hb =>
      simpa only [substVars, substVars_renameLabels] using
        SubstitutionEquiv.cfgOutward R (hr.substVars (valuesTyped hσ))
          (fun i => (hb i).substVars (valuesTyped (liftValues hσ _)))

private theorem equivalentLiftVars {Γ : VCtx τ} {L K : LCtx τ} {σ υ : Nat → Region Φ}
    (h : ∀ ⦃ℓ A⦄, At L ℓ A → SubstitutionEquiv (A :: Γ) (σ ℓ) (υ ℓ) K) (B : τ) :
    ∀ ⦃ℓ A⦄, At L ℓ A →
      SubstitutionEquiv (A :: B :: Γ) (liftLSubstVars σ ℓ) (liftLSubstVars υ ℓ) K := by
  intro ℓ A hℓ
  simp only [liftLSubstVars, renameVars_eq_substVars]
  exact substitutionEquiv_substVars (h hℓ) (fun _ _ hi => .var (((Silmaril.Isotope.SSA.Ren.wk Γ B).lift A) hi))

private theorem equivalentLift {Γ : VCtx τ} {L K : LCtx τ} {σ υ : Nat → Region Φ}
    (h : ∀ ⦃ℓ A⦄, At L ℓ A → SubstitutionEquiv (A :: Γ) (σ ℓ) (υ ℓ) K) (B : τ) :
    ∀ ⦃ℓ A⦄, At (B :: L) ℓ A → SubstitutionEquiv (A :: Γ) (liftLSubst σ ℓ) (liftLSubst υ ℓ) (B :: K) := by
  intro ℓ A hℓ
  cases ℓ with
  | zero =>
      cases Option.some.inj hℓ
      exact .base (.refl (.br rfl (.var rfl)))
  | succ ℓ =>
      change SubstitutionEquiv (A :: Γ) ((σ ℓ).renameLabels Nat.succ) ((υ ℓ).renameLabels Nat.succ) (B :: K)
      rw [renameLabels_eq_lsubst, renameLabels_eq_lsubst]
      apply substitutionEquiv_lsubst (h hℓ)
      intro j D hj
      exact .br ((Silmaril.Isotope.SSA.Ren.wk K B) hj) (.var rfl)

private theorem equivalentAppend {Γ : VCtx τ} {L K : LCtx τ} {σ υ : Nat → Region Φ}
    (h : ∀ ⦃ℓ A⦄, At L ℓ A → SubstitutionEquiv (A :: Γ) (σ ℓ) (υ ℓ) K) (Ξ : LCtx τ) :
    ∀ ⦃ℓ A⦄, At (Ξ ++ L) ℓ A →
      SubstitutionEquiv (A :: Γ) (liftLSubstN Ξ.length σ ℓ) (liftLSubstN Ξ.length υ ℓ) (Ξ ++ K) := by
  induction Ξ with
  | nil => exact h
  | cons B Ξ ih => exact equivalentLift ih B

theorem lsubst_substitutionEquiv {Γ : VCtx τ} {L K : LCtx τ} {r : Region Φ}
    (hr : ValueBranches Γ r L) {σ υ : Nat → Region Φ}
    (h : ∀ ⦃ℓ A⦄, At L ℓ A → SubstitutionEquiv (A :: Γ) (σ ℓ) (υ ℓ) K) :
    SubstitutionEquiv Γ (r.lsubst σ) (r.lsubst υ) K := by
  induction hr generalizing K σ υ with
  | br hℓ ha =>
      apply substitutionEquiv_substVars (h hℓ)
      intro i A hi
      cases i with
      | zero =>
          cases Option.some.inj hi
          exact ha
      | succ i => exact .var hi
  | let₁ ha _ ih => exact .let₁ ha (ih (equivalentLiftVars h _))
  | let₂ ha _ ih => exact .let₂ ha (ih (equivalentLiftVars (equivalentLiftVars h _) _))
  | case ha _ _ ihl ihr => exact .case ha (ihl (equivalentLiftVars h _)) (ihr (equivalentLiftVars h _))
  | cfg R _ _ ihe ihb =>
      have hlabels := equivalentAppend h (List.ofFn R)
      simp only [List.length_ofFn] at hlabels
      exact .cfg R (ihe hlabels) (fun i => ihb i (equivalentLiftVars hlabels _))

theorem compLSubst_substitutionEquiv {Γ : VCtx τ} {L K P : LCtx τ}
    {σ σ' υ υ' : Nat → Region Φ}
    (hσ : ∀ ⦃ℓ A⦄, At L ℓ A → SubstitutionEquiv (A :: Γ) (σ ℓ) (σ' ℓ) K)
    (hυ : ∀ ⦃ℓ A⦄, At K ℓ A → SubstitutionEquiv (A :: Γ) (υ ℓ) (υ' ℓ) P)
    (hvalues : ∀ ⦃ℓ A⦄, At L ℓ A → ValueBranches (A :: Γ) (σ ℓ) K) :
    ∀ ⦃ℓ A⦄, At L ℓ A → SubstitutionEquiv (A :: Γ) (compLSubst σ υ ℓ) (compLSubst σ' υ' ℓ) P := by
  intro ℓ A hℓ
  have hlift := equivalentLiftVars hυ A
  exact .trans (lsubst_substitutionEquiv (hvalues hℓ) hlift)
    (substitutionEquiv_lsubst (hσ hℓ) (fun _ _ hi => (substitutionEquiv_typed (hlift hi)).2))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
