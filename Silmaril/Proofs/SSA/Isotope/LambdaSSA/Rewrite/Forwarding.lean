module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Substitution.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.TheoryTyping
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.TheorySubstitution
import Silmaril.Raw.SSA.Isotope.LambdaSSA.ContinuationLaws

/-! # Congruence under native branch-forwarding label substitution -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.DeBruijn (lift)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v}

theorem forwardLiftVars {Γ : VCtx τ} {L K : LCtx τ} {σ : Nat → Region Φ}
    (hσ : LSubst.Forwards Γ L K σ) (D : τ) :
    LSubst.Forwards (D :: Γ) L K (liftLSubstVars σ) := by
  intro ℓ A hℓ
  obtain ⟨j, b, B, heq, hj, hb⟩ := hσ hℓ
  refine ⟨j, b.rename (lift Nat.succ), B, ?_, hj, ?_⟩
  · simp [liftLSubstVars, heq, renameVars]
  · exact branchValue_rename hb ((Silmaril.Isotope.SSA.Ren.wk Γ D).lift A)

private theorem forwardLift {Γ : VCtx τ} {L K : LCtx τ} {σ : Nat → Region Φ}
    (hσ : LSubst.Forwards Γ L K σ) (D : τ) :
    LSubst.Forwards Γ (D :: L) (D :: K) (liftLSubst σ) := by
  intro ℓ A hℓ
  cases ℓ with
  | zero =>
      cases Option.some.inj hℓ
      exact ⟨0, .var 0, D, rfl, rfl, .var rfl⟩
  | succ ℓ =>
      obtain ⟨j, b, B, heq, hj, hb⟩ := hσ hℓ
      exact ⟨j + 1, b, B, by simp [liftLSubst, heq, renameLabels], hj, hb⟩

private theorem forwardAppend {Γ : VCtx τ} {L K : LCtx τ} {σ : Nat → Region Φ}
    (hσ : LSubst.Forwards Γ L K σ) (Ξ : LCtx τ) :
    LSubst.Forwards Γ (Ξ ++ L) (Ξ ++ K) (liftLSubstN Ξ.length σ) := by
  induction Ξ with
  | nil => exact hσ
  | cons D Ξ ih => exact forwardLift ih D

private theorem forwardBlocks {Γ : VCtx τ} {L K : LCtx τ} {σ : Nat → Region Φ}
    (hσ : LSubst.Forwards Γ L K σ) {n : Nat} (R : Fin n → τ) :
    LSubst.Forwards Γ (List.ofFn R ++ L) (List.ofFn R ++ K) (liftLSubstN n σ) := by
  simpa only [List.length_ofFn] using forwardAppend hσ (List.ofFn R)

theorem liftAtLocal (σ : Nat → Region Φ) {ℓ n : Nat} (h : ℓ < n) :
    liftLSubstN n σ ℓ = labelId ℓ := by
  induction n generalizing ℓ with
  | zero => exact (Nat.not_lt_zero _ h).elim
  | succ n ih =>
      cases ℓ with
      | zero => rfl
      | succ ℓ =>
          change (liftLSubstN n σ ℓ).renameLabels Nat.succ = labelId (ℓ + 1)
          rw [ih (Nat.lt_of_succ_lt_succ h)]
          rfl

theorem liftAtExit (σ : Nat → Region Φ) (n ℓ : Nat) :
    liftLSubstN n σ (n + ℓ) = (σ ℓ).renameLabels (fun j => n + j) := by
  induction n with
  | zero =>
      have h : (fun j : Nat => 0 + j) = id := funext Nat.zero_add
      rw [h, renameLabels_id]
      simp only [liftLSubstN, Nat.zero_add]
  | succ n ih =>
      rw [Nat.succ_add]
      change (liftLSubstN n σ (n + ℓ)).renameLabels Nat.succ = _
      rw [ih, renameLabels_comp]
      congr 1
      funext j
      exact (Nat.succ_add n j).symm

variable [HasTy Φ τ]

private theorem forwardsTyped {Γ : VCtx τ} {L K : LCtx τ} {σ : Nat → Region Φ}
    (hσ : LSubst.Forwards Γ L K σ) : LSubst.HasType Γ L K σ := by
  intro ℓ A hℓ
  obtain ⟨j, b, B, heq, hj, hb⟩ := hσ hℓ
  rw [heq]
  exact .br hj hb.hasType

private theorem cfgEquiv_lsubst {Γ : VCtx τ} {L K : LCtx τ} {r s : Region Φ}
    (h : CfgEquiv Γ r s L) {σ : Nat → Region Φ} (hσ : LSubst.Forwards Γ L K σ) :
    CfgEquiv Γ (r.lsubst σ) (s.lsubst σ) K := by
  induction h generalizing K σ with
  | refl hr => exact .refl (hr.lsubst (forwardsTyped hσ))
  | symm _ ih => exact .symm (ih hσ)
  | trans _ _ ihr ihs => exact .trans (ihr hσ) (ihs hσ)
  | let₁ ha _ ih => exact .let₁ ha (ih (forwardLiftVars hσ _))
  | let₂ ha _ ih => exact .let₂ ha (ih (forwardLiftVars (forwardLiftVars hσ _) _))
  | case ha _ _ ihl ihr => exact .case ha (ihl (forwardLiftVars hσ _)) (ihr (forwardLiftVars hσ _))
  | cfg R _ _ ihe ihb =>
      exact .cfg R (ihe (forwardBlocks hσ R)) (fun i => ihb i (forwardLiftVars (forwardBlocks hσ R) _))
  | cfgZero he _ => exact .cfgZero (he.lsubst (forwardsTyped hσ)) _
  | @cfgBrExit n _ _ ℓ A a blocks R hℓ ha hb =>
      obtain ⟨j, b, B, heq, hj, hvalue⟩ := hσ hℓ
      have harg := branchValue_singleSubst ha hvalue
      have hblocks := fun i =>
        (hb i).lsubst (forwardsTyped (forwardLiftVars (forwardBlocks hσ R) (R i)))
      simpa only [lsubst, liftAtExit, heq, renameLabels, substVars] using
        CfgEquiv.cfgBrExit R hj harg hblocks
  | @cfgBrLocal n _ _ a blocks R i ha hb =>
      have hblocks := fun j =>
        (hb j).lsubst (forwardsTyped (forwardLiftVars (forwardBlocks hσ R) (R j)))
      simpa only [lsubst, liftAtLocal σ i.isLt, labelId, substVars, Tm.subst, Tm.consSubst] using
        CfgEquiv.cfgBrLocal R i ha hblocks

theorem rewriteEquiv_lsubst {Γ : VCtx τ} {L K : LCtx τ} {r s : Region Φ}
    (h : RewriteEquiv Γ r s L) {σ : Nat → Region Φ} (hσ : LSubst.Forwards Γ L K σ) :
    RewriteEquiv Γ (r.lsubst σ) (s.lsubst σ) K := by
  induction h generalizing K σ with
  | entry h => exact .entry (cfgEquiv_lsubst h hσ)
  | symm _ ih => exact .symm (ih hσ)
  | trans _ _ ihr ihs => exact .trans (ihr hσ) (ihs hσ)
  | let₁ ha _ ih => exact .let₁ ha (ih (forwardLiftVars hσ _))
  | let₂ ha _ ih => exact .let₂ ha (ih (forwardLiftVars (forwardLiftVars hσ _) _))
  | case ha _ _ ihl ihr => exact .case ha (ihl (forwardLiftVars hσ _)) (ihr (forwardLiftVars hσ _))
  | cfg R _ _ ihe ihb =>
      exact .cfg R (ihe (forwardBlocks hσ R)) (fun i => ihb i (forwardLiftVars (forwardBlocks hσ R) _))
  | @letBr Γ a A b B L ℓ ha hb hℓ =>
      obtain ⟨j, c, D, heq, hj, hc⟩ := hσ hℓ
      have harg := branchValue_singleSubst hb
        (branchValue_rename hc ((Silmaril.Isotope.SSA.Ren.wk Γ A).lift B))
      have he := lsubst_single (.br ℓ b) a σ
      change (σ ℓ).substVars (Tm.singleSubst (b.subst (Tm.singleSubst a))) =
        ((liftLSubstVars σ ℓ).substVars (Tm.singleSubst b)).substVars (Tm.singleSubst a) at he
      change RewriteEquiv Γ (.let₁ a ((liftLSubstVars σ ℓ).substVars (Tm.singleSubst b)))
        ((σ ℓ).substVars (Tm.singleSubst (b.subst (Tm.singleSubst a)))) K
      rw [he]
      simpa only [liftLSubstVars, heq, renameVars, substVars] using
        RewriteEquiv.letBr ha harg hj
  | caseInl ha hl hr =>
      exact .caseInl ha (hl.lsubst (forwardsTyped (forwardLiftVars hσ _)))
        (hr.lsubst (forwardsTyped (forwardLiftVars hσ _)))
  | caseInr hb hl hr =>
      exact .caseInr hb (hl.lsubst (forwardsTyped (forwardLiftVars hσ _)))
        (hr.lsubst (forwardsTyped (forwardLiftVars hσ _)))

theorem rewriteEquiv_renameLabels {Γ : VCtx τ} {L K : LCtx τ} {r s : Region Φ}
    (h : RewriteEquiv Γ r s L) {ρ : Nat → Nat} (hρ : Silmaril.Isotope.SSA.Ren L K ρ) :
    RewriteEquiv Γ (r.renameLabels ρ) (s.renameLabels ρ) K := by
  rw [renameLabels_eq_lsubst, renameLabels_eq_lsubst]
  apply rewriteEquiv_lsubst h
  intro ℓ A hℓ
  exact ⟨ρ ℓ, .var 0, A, rfl, hρ hℓ, .var rfl⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
