module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.TheoryTyping
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Labels
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Forwarding

/-! # Native closure under arbitrary typed continuation substitution -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

omit [TypeFormers τ] in
private theorem outwardRen {n : Nat} (R : Fin n → τ) (L : LCtx τ) :
    Ren L (List.ofFn R ++ L) (fun j => n + j) :=
  fun _ _ hi => exitAt R hi

theorem substitutionEquiv_typed {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : SubstitutionEquiv Γ r s L) : Region.HasType Γ r L ∧ Region.HasType Γ s L := by
  induction h with
  | base h => exact h.typed
  | symm _ ih => exact ⟨ih.2, ih.1⟩
  | trans _ _ ihr ihs => exact ⟨ihr.1, ihs.2⟩
  | let₁ ha _ ih => exact ⟨.let₁ ha ih.1, .let₁ ha ih.2⟩
  | let₂ ha _ ih => exact ⟨.let₂ ha ih.1, .let₂ ha ih.2⟩
  | case ha _ _ ihl ihr => exact ⟨.case ha ihl.1 ihr.1, .case ha ihl.2 ihr.2⟩
  | cfg R _ _ ihe ihb => exact ⟨.cfg R ihe.1 (fun i => (ihb i).1), .cfg R ihe.2 (fun i => (ihb i).2)⟩
  | letValue ha hr => exact ⟨.let₁ ha.hasType hr, hr.substVars (Tm.Subst.HasType.single ha.hasType)⟩
  | cfgOutward R hr hb => exact ⟨.cfg R (hr.renameLabels (outwardRen R _)) hb, hr⟩

private theorem typedLiftBlocks {Γ : VCtx τ} {L K : LCtx τ} {σ : Nat → Region Φ}
    (hσ : LSubst.HasType Γ L K σ) {n : Nat} (R : Fin n → τ) :
    LSubst.HasType Γ (List.ofFn R ++ L) (List.ofFn R ++ K) (liftLSubstN n σ) := by
  simpa only [List.length_ofFn] using hσ.append (List.ofFn R)

private theorem lsubst_outward (r : Region Φ) (σ : Nat → Region Φ) (n : Nat) :
    (r.renameLabels (fun j => n + j)).lsubst (liftLSubstN n σ) =
      (r.lsubst σ).renameLabels (fun j => n + j) := by
  rw [lsubst_renameLabels, renameLabels_lsubst]
  congr 1
  funext j
  exact liftAtExit σ n j

private theorem cfgEquiv_lsubst_closed {Γ : VCtx τ} {L K : LCtx τ} {r s : Region Φ}
    (h : CfgEquiv Γ r s L) {σ : Nat → Region Φ} (hσ : LSubst.HasType Γ L K σ) :
    SubstitutionEquiv Γ (r.lsubst σ) (s.lsubst σ) K := by
  induction h generalizing K σ with
  | refl hr => exact .base (.refl (hr.lsubst hσ))
  | symm _ ih => exact .symm (ih hσ)
  | trans _ _ ihr ihs => exact .trans (ihr hσ) (ihs hσ)
  | let₁ ha _ ih => exact .let₁ ha (ih (hσ.liftVars _))
  | let₂ ha _ ih => exact .let₂ ha (ih ((hσ.liftVars _).liftVars _))
  | case ha _ _ ihl ihr => exact .case ha (ihl (hσ.liftVars _)) (ihr (hσ.liftVars _))
  | cfg R _ _ ihe ihb =>
      exact .cfg R (ihe (typedLiftBlocks hσ R)) (fun i => ihb i ((typedLiftBlocks hσ R).liftVars _))
  | cfgZero he _ => exact .base (.entry (.cfgZero (he.lsubst hσ) _))
  | cfgBrExit R hℓ ha hb =>
      have hblocks := fun i => (hb i).lsubst ((typedLiftBlocks hσ R).liftVars (R i))
      have he := (hσ hℓ).substVars (Tm.Subst.HasType.single ha.hasType)
      simpa only [lsubst, liftAtExit, substVars_renameLabels] using
        SubstitutionEquiv.cfgOutward R he hblocks
  | cfgBrLocal R i ha hb =>
      have hblocks := fun j => (hb j).lsubst ((typedLiftBlocks hσ R).liftVars (R j))
      simpa only [lsubst, liftAtLocal σ i.isLt, labelId, substVars, Tm.subst, Tm.consSubst] using
        SubstitutionEquiv.base (.entry (.cfgBrLocal R i ha hblocks))

private theorem rewriteEquiv_lsubst_closed {Γ : VCtx τ} {L K : LCtx τ} {r s : Region Φ}
    (h : RewriteEquiv Γ r s L) {σ : Nat → Region Φ} (hσ : LSubst.HasType Γ L K σ) :
    SubstitutionEquiv Γ (r.lsubst σ) (s.lsubst σ) K := by
  induction h generalizing K σ with
  | entry h => exact cfgEquiv_lsubst_closed h hσ
  | symm _ ih => exact .symm (ih hσ)
  | trans _ _ ihr ihs => exact .trans (ihr hσ) (ihs hσ)
  | let₁ ha _ ih => exact .let₁ ha (ih (hσ.liftVars _))
  | let₂ ha _ ih => exact .let₂ ha (ih ((hσ.liftVars _).liftVars _))
  | case ha _ _ ihl ihr => exact .case ha (ihl (hσ.liftVars _)) (ihr (hσ.liftVars _))
  | cfg R _ _ ihe ihb =>
      exact .cfg R (ihe (typedLiftBlocks hσ R)) (fun i => ihb i ((typedLiftBlocks hσ R).liftVars _))
  | @letBr Γ a A b B L ℓ ha hb hℓ =>
      exact (lsubst_single (.br ℓ b) a σ).symm ▸
        SubstitutionEquiv.letValue ha ((Region.HasType.br hℓ hb.hasType).lsubst (hσ.liftVars A))
  | caseInl ha hl hr => exact .base (.caseInl ha (hl.lsubst (hσ.liftVars _)) (hr.lsubst (hσ.liftVars _)))
  | caseInr hb hl hr => exact .base (.caseInr hb (hl.lsubst (hσ.liftVars _)) (hr.lsubst (hσ.liftVars _)))

theorem substitutionEquiv_lsubst {Γ : VCtx τ} {L K : LCtx τ} {r s : Region Φ}
    (h : SubstitutionEquiv Γ r s L) {σ : Nat → Region Φ} (hσ : LSubst.HasType Γ L K σ) :
    SubstitutionEquiv Γ (r.lsubst σ) (s.lsubst σ) K := by
  induction h generalizing K σ with
  | base h => exact rewriteEquiv_lsubst_closed h hσ
  | symm _ ih => exact .symm (ih hσ)
  | trans _ _ ihr ihs => exact .trans (ihr hσ) (ihs hσ)
  | let₁ ha _ ih => exact .let₁ ha (ih (hσ.liftVars _))
  | let₂ ha _ ih => exact .let₂ ha (ih ((hσ.liftVars _).liftVars _))
  | case ha _ _ ihl ihr => exact .case ha (ihl (hσ.liftVars _)) (ihr (hσ.liftVars _))
  | cfg R _ _ ihe ihb =>
      exact .cfg R (ihe (typedLiftBlocks hσ R)) (fun i => ihb i ((typedLiftBlocks hσ R).liftVars _))
  | @letValue Γ a A r L ha hr =>
      exact (lsubst_single r a σ).symm ▸ SubstitutionEquiv.letValue ha (hr.lsubst (hσ.liftVars A))
  | cfgOutward R hr hb =>
      have hblocks := fun i => (hb i).lsubst ((typedLiftBlocks hσ R).liftVars (R i))
      simpa only [lsubst, lsubst_outward] using SubstitutionEquiv.cfgOutward R (hr.lsubst hσ) hblocks

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
