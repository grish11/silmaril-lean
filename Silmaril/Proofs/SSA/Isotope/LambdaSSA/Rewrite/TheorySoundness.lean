module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Soundness
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.LetBranch
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Combinators

/-! # Soundness of the typed let and CFG equations -/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : Functor V C) [StrongElgotFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]

private theorem caseInl_common {Γ : VCtx τ} {L : LCtx τ} {a : Tm Φ} {A B : τ} {l r : Region Φ}
    (ha : Tm.HasType Γ a A) (hl : Region.HasType (A :: Γ) l L) (hr : Region.HasType (B :: Γ) r L) :
    ∃ f, RegionDenotes J M (.case (.inl ha) hl hr) f ∧ RegionDenotes J M (.let₁ ha hl) f := by
  obtain ⟨f, df⟩ := denotes_exists J M ha
  obtain ⟨fl, dl⟩ := regionDenotes_exists J M hl
  obtain ⟨fr, dr⟩ := regionDenotes_exists J M hr
  have d := RegionDenotes.case (.inl df) dl dr
  have hinj : (f ≫ J.map (coprod.inl ≫ (M.coprodIso A B).inv)) ≫ J.map (M.coprodIso A B).hom =
      f ≫ J.map (coprod.inl : M.obj A ⟶ M.obj A ⨿ M.obj B) := by
    rw [Category.assoc, ← J.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hinj, case_inl J f fl fr] at d
  exact ⟨_, d, .let₁ df dl⟩

private theorem caseInr_common {Γ : VCtx τ} {L : LCtx τ} {b : Tm Φ} {A B : τ} {l r : Region Φ}
    (hb : Tm.HasType Γ b B) (hl : Region.HasType (A :: Γ) l L) (hr : Region.HasType (B :: Γ) r L) :
    ∃ f, RegionDenotes J M (.case (.inr hb) hl hr) f ∧ RegionDenotes J M (.let₁ hb hr) f := by
  obtain ⟨f, df⟩ := denotes_exists J M hb
  obtain ⟨fl, dl⟩ := regionDenotes_exists J M hl
  obtain ⟨fr, dr⟩ := regionDenotes_exists J M hr
  have d := RegionDenotes.case (.inr df) dl dr
  have hinj : (f ≫ J.map (coprod.inr ≫ (M.coprodIso A B).inv)) ≫ J.map (M.coprodIso A B).hom =
      f ≫ J.map (coprod.inr : M.obj B ⟶ M.obj A ⨿ M.obj B) := by
    rw [Category.assoc, ← J.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hinj, case_inr J f fl fr] at d
  exact ⟨_, d, .let₁ df dr⟩

variable [RegionTypingCoherent (Φ := Φ) J M]

theorem rewriteEquiv_common {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : Region.RewriteEquiv Γ r s L) :
    ∃ (hr : Region.HasType Γ r L) (hs : Region.HasType Γ s L),
      ∃ f, RegionDenotes J M hr f ∧ RegionDenotes J M hs f := by
  induction h with
  | entry h => exact cfgEquiv_common J M h
  | symm _ ih =>
      obtain ⟨hr, hs, f, dr, ds⟩ := ih
      exact ⟨hs, hr, f, ds, dr⟩
  | trans _ _ ihr ihs =>
      obtain ⟨hr, hs, f, dr, ds⟩ := ihr
      obtain ⟨_, ht, g, ds', dt⟩ := ihs
      have hfg : f = g := RegionTypingCoherent.denotes_eq (h := hs) ds ds'
      exact ⟨hr, ht, g, hfg ▸ dr, dt⟩
  | let₁ ha _ ih =>
      obtain ⟨hr, hs, f, dr, ds⟩ := ih
      have da := denote_spec J M ha
      exact ⟨.let₁ ha hr, .let₁ ha hs, _, .let₁ da dr, .let₁ da ds⟩
  | let₂ ha _ ih =>
      obtain ⟨hr, hs, f, dr, ds⟩ := ih
      have da := denote_spec J M ha
      exact ⟨.let₂ ha hr, .let₂ ha hs, _, .let₂ da dr, .let₂ da ds⟩
  | case ha _ _ ihl ihr =>
      obtain ⟨hl, hl', fl, dl, dl'⟩ := ihl
      obtain ⟨hr, hr', fr, dr, dr'⟩ := ihr
      have da := denote_spec J M ha
      exact ⟨.case ha hl hr, .case ha hl' hr', _, .case da dl dr, .case da dl' dr'⟩
  | @cfg n _ _ _ _ _ _ R _ _ ihe ihb =>
      obtain ⟨he, he', fe, de, de'⟩ := ihe
      choose hb hb' fb db using ihb
      cases n with
      | zero =>
          exact ⟨.cfg R he hb, .cfg R he' hb', fe, .cfgZero he hb de, .cfgZero he' hb' de'⟩
      | succ n =>
          obtain ⟨_, dc⟩ := collectiveDenotes_exists_succ J M n _ R _ fb
          exact ⟨.cfg R he hb, .cfg R he' hb', _,
            .cfg he hb de (fun i => (db i).1) dc, .cfg he' hb' de' (fun i => (db i).2) dc⟩
  | letBr ha hb hl => exact letBr_common J M ha hb hl
  | caseInl ha hl hr => exact ⟨.case (.inl ha) hl hr, .let₁ ha hl, caseInl_common J M ha hl hr⟩
  | caseInr hb hl hr => exact ⟨.case (.inr hb) hl hr, .let₁ hb hr, caseInr_common J M hb hl hr⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
