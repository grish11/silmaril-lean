module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Substitution.Thms
public import Silmaril.Raw.SSA.Isotope.LambdaSSA.ContinuationLaws
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Forwarding

/-! # Substitution of equivalent continuations at constructor-valued exits -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.SSA (Ren)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

theorem valueBranches_typed {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    (hr : ValueBranches Γ r L) : Region.HasType Γ r L := by
  induction hr with
  | br hℓ ha => exact .br hℓ ha.hasType
  | let₁ ha _ ih => exact .let₁ ha ih
  | let₂ ha _ ih => exact .let₂ ha ih
  | case ha _ _ ihl ihr => exact .case ha ihl ihr
  | cfg R _ _ ihe ihb => exact .cfg R ihe ihb

private theorem equivalentLiftVars {Γ : VCtx τ} {L K : LCtx τ} {σ σ' : Nat → Region Φ}
    (h : LSubst.Equivalent Γ L K σ σ') (B : τ) :
    LSubst.Equivalent (B :: Γ) L K (liftLSubstVars σ) (liftLSubstVars σ') := by
  intro ℓ A hℓ
  simp only [liftLSubstVars, renameVars_eq_substVars]
  exact (h hℓ).substVars (fun _ _ hi => .var (((Ren.wk Γ B).lift A) hi))

private theorem equivalentLift {Γ : VCtx τ} {L K : LCtx τ} {σ σ' : Nat → Region Φ}
    (h : LSubst.Equivalent Γ L K σ σ') (B : τ) :
    LSubst.Equivalent Γ (B :: L) (B :: K) (liftLSubst σ) (liftLSubst σ') := by
  intro ℓ A hℓ
  cases ℓ with
  | zero =>
      cases Option.some.inj hℓ
      exact .refl (.br rfl (.var rfl))
  | succ ℓ => exact (h hℓ).renameLabels (Ren.wk K B)

private theorem equivalentAppend {Γ : VCtx τ} {L K : LCtx τ} {σ σ' : Nat → Region Φ}
    (h : LSubst.Equivalent Γ L K σ σ') (Ξ : LCtx τ) :
    LSubst.Equivalent Γ (Ξ ++ L) (Ξ ++ K) (liftLSubstN Ξ.length σ) (liftLSubstN Ξ.length σ') := by
  induction Ξ with
  | nil => exact h
  | cons B Ξ ih => exact equivalentLift ih B

theorem lsubst_equivalent {Γ : VCtx τ} {L K : LCtx τ} {r : Region Φ}
    (hr : ValueBranches Γ r L) {σ σ' : Nat → Region Φ} (h : LSubst.Equivalent Γ L K σ σ') :
    RewriteEquiv Γ (r.lsubst σ) (r.lsubst σ') K := by
  induction hr generalizing K σ σ' with
  | br hℓ ha =>
      apply (h hℓ).substVars
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

theorem equivalentComp {Γ : VCtx τ} {L K P : LCtx τ} {σ σ' υ υ' : Nat → Region Φ}
    (hσ : LSubst.Equivalent Γ L K σ σ') (hυ : LSubst.Equivalent Γ K P υ υ')
    (hforward : LSubst.Forwards Γ K P υ)
    (hvalues : ∀ ⦃ℓ A⦄, At L ℓ A → ValueBranches (A :: Γ) (σ' ℓ) K) :
    LSubst.Equivalent Γ L P (compLSubst σ υ) (compLSubst σ' υ') := by
  intro ℓ A hℓ
  exact ((hσ hℓ).lsubst (forwardLiftVars hforward A)).trans
    (lsubst_equivalent (hvalues hℓ) (equivalentLiftVars hυ A))

theorem rewriteEquiv_linkExits {Γ : VCtx τ} {L K : LCtx τ} {r s : Region Φ}
    (h : RewriteEquiv Γ r s L) {σ σ' : Nat → Region Φ} (hs : LSubst.Equivalent Γ L K σ σ') :
    RewriteEquiv Γ (r.linkExits L σ) (s.linkExits L σ') K := by
  have hprefix : List.ofFn (fun i : Fin L.length => L.get i) = L := List.ofFn_get L
  have hin : Ren L (List.ofFn (fun i : Fin L.length => L.get i) ++ K) id := by
    intro ℓ A hℓ
    have hlt := (List.getElem?_eq_some_iff.mp hℓ).1
    simpa only [hprefix, id_eq, At, List.getElem?_append_left hlt] using hℓ
  have hout : Ren K (List.ofFn (fun i : Fin L.length => L.get i) ++ K)
      (fun j => L.length + j) := by
    intro j A hj
    simpa [hprefix, At, List.getElem?_append_right] using hj
  refine .cfg (fun i : Fin L.length => L.get i) ?_ (fun i => ?_)
  · simpa only [renameLabels_id] using h.renameLabels hin
  · exact (hs (show At L i (L.get i) by simp [At])).renameLabels hout

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
