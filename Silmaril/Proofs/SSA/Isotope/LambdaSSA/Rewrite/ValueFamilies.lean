module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.TheoryTyping
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.TheorySubstitution

/-! # Stability of constructor-valued branches under substitution -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

private theorem valueBranches_substVars {Γ Δ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    (hr : ValueBranches Γ r L) {σ : Nat → Tm Φ}
    (hσ : ∀ ⦃i A⦄, At Γ i A → Tm.BranchValue Δ (σ i) A) :
    ValueBranches Δ (r.substVars σ) L := by
  induction hr generalizing Δ σ with
  | br hℓ ha => exact .br hℓ (branchValue_subst ha hσ)
  | let₁ ha _ ih => exact .let₁ (ha.subst (valuesTyped hσ)) (ih (liftValues hσ _))
  | let₂ ha _ ih => exact .let₂ (ha.subst (valuesTyped hσ)) (ih (liftValues (liftValues hσ _) _))
  | case ha _ _ ihl ihr =>
      exact .case (ha.subst (valuesTyped hσ)) (ihl (liftValues hσ _)) (ihr (liftValues hσ _))
  | cfg R _ _ ihe ihb => exact .cfg R (ihe hσ) (fun i => ihb i (liftValues hσ _))

private theorem valueBranches_renameLabels {Γ : VCtx τ} {L K : LCtx τ} {r : Region Φ}
    (hr : ValueBranches Γ r L) {ρ : Nat → Nat} (hρ : Ren L K ρ) :
    ValueBranches Γ (r.renameLabels ρ) K := by
  induction hr generalizing K ρ with
  | br hℓ ha => exact .br (hρ hℓ) ha
  | let₁ ha _ ih => exact .let₁ ha (ih hρ)
  | let₂ ha _ ih => exact .let₂ ha (ih hρ)
  | case ha _ _ ihl ihr => exact .case ha (ihl hρ) (ihr hρ)
  | cfg R _ _ ihe ihb =>
      have hlabels := Silmaril.Isotope.SSA.Ren.append hρ (List.ofFn R)
      simp only [List.length_ofFn] at hlabels
      exact .cfg R (ihe hlabels) (fun i => ihb i hlabels)

theorem valueFamily_liftVars {Γ : VCtx τ} {L K : LCtx τ} {σ : Nat → Region Φ}
    (hσ : LSubst.ValueFamily Γ L K σ) (D : τ) :
    LSubst.ValueFamily (D :: Γ) L K (liftLSubstVars σ) := by
  intro ℓ A hi
  simp only [liftLSubstVars, renameVars_eq_substVars]
  exact valueBranches_substVars (hσ hi)
    (fun _ _ h => .var (((Silmaril.Isotope.SSA.Ren.wk Γ D).lift A) h))

private theorem valueFamily_lift {Γ : VCtx τ} {L K : LCtx τ} {σ : Nat → Region Φ}
    (hσ : LSubst.ValueFamily Γ L K σ) (D : τ) :
    LSubst.ValueFamily Γ (D :: L) (D :: K) (liftLSubst σ) := by
  intro ℓ A hi
  cases ℓ with
  | zero =>
      cases Option.some.inj hi
      exact .br rfl (.var rfl)
  | succ ℓ => exact valueBranches_renameLabels (hσ hi) (Silmaril.Isotope.SSA.Ren.wk K D)

private theorem valueFamily_append {Γ : VCtx τ} {L K : LCtx τ} {σ : Nat → Region Φ}
    (hσ : LSubst.ValueFamily Γ L K σ) (Ξ : LCtx τ) :
    LSubst.ValueFamily Γ (Ξ ++ L) (Ξ ++ K) (liftLSubstN Ξ.length σ) := by
  induction Ξ with
  | nil => exact hσ
  | cons D Ξ ih => exact valueFamily_lift ih D

theorem valueBranches_lsubst {Γ : VCtx τ} {L K : LCtx τ} {r : Region Φ}
    (hr : ValueBranches Γ r L) {σ : Nat → Region Φ} (hσ : LSubst.ValueFamily Γ L K σ) :
    ValueBranches Γ (r.lsubst σ) K := by
  induction hr generalizing K σ with
  | br hℓ ha =>
      apply valueBranches_substVars (hσ hℓ)
      intro i A hi
      cases i with
      | zero =>
          cases Option.some.inj hi
          exact ha
      | succ i => exact .var hi
  | let₁ ha _ ih => exact .let₁ ha (ih (valueFamily_liftVars hσ _))
  | let₂ ha _ ih => exact .let₂ ha (ih (valueFamily_liftVars (valueFamily_liftVars hσ _) _))
  | case ha _ _ ihl ihr => exact .case ha (ihl (valueFamily_liftVars hσ _)) (ihr (valueFamily_liftVars hσ _))
  | cfg R _ _ ihe ihb =>
      have hlabels := valueFamily_append hσ (List.ofFn R)
      simp only [List.length_ofFn] at hlabels
      exact .cfg R (ihe hlabels) (fun i => ihb i (valueFamily_liftVars hlabels _))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
