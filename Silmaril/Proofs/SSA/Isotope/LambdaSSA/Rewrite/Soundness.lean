module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Combinators
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Labels
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Typing

/-! # Denotation of typed CFG entry rewrites -/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (caseWithContext contextualLoop extend)
local notation "bindArrow" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]

section BranchValue

variable (J : Functor V C) [DistributiveFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]

theorem branchValue_denotes {Γ : VCtx τ} {a : Tm Φ} {A : τ} (h : Tm.BranchValue Γ a A) :
    ∃ (ht : Tm.HasType Γ a A) (p : ctxObj M Γ ⟶ M.obj A), Denotes J M ht (J.map p) := by
  induction h with
  | var hi => exact ⟨_, _, .var hi⟩
  | unit => exact ⟨_, _, .unit⟩
  | pair _ _ iha ihb =>
      obtain ⟨ha, p, dp⟩ := iha
      obtain ⟨hb, q, dq⟩ := ihb
      refine ⟨.pair ha hb, CartesianMonoidalCategory.lift p q ≫ (M.productIso _ _).inv, ?_⟩
      rw [J.map_comp, ← pair_map]
      exact .pair dp dq
  | inl _ ih =>
      obtain ⟨ha, p, dp⟩ := ih
      refine ⟨.inl ha, p ≫ coprod.inl ≫ (M.coprodIso _ _).inv, ?_⟩
      rw [J.map_comp]
      exact .inl dp
  | inr _ ih =>
      obtain ⟨hb, p, dp⟩ := ih
      refine ⟨.inr hb, p ≫ coprod.inr ≫ (M.coprodIso _ _).inv, ?_⟩
      rw [J.map_comp]
      exact .inr dp

end BranchValue

section Cfg

variable [Iteration C] [ElgotCategory C]
  (J : Functor V C) [StrongElgotFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]

set_option backward.isDefEq.respectTransparency false in
theorem cfgBrExit_map_common {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {ℓ : Nat} {a : Tm Φ}
    {A : τ} {blocks : Fin (n + 1) → Region Φ}
    (R : Fin (n + 1) → τ) (hℓ : At L ℓ A) (ha : Tm.HasType Γ a A)
    (p : ctxObj M Γ ⟶ M.obj A) (dp : Denotes J M ha (J.map p))
    (hb : ∀ i, Region.HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L)) :
    ∃ (hs : Region.HasType Γ (.cfg (.br (n + 1 + ℓ) a) (n + 1) blocks) L)
      (ht : Region.HasType Γ (.br ℓ a) L), ∃ f, RegionDenotes J M hs f ∧ RegionDenotes J M ht f := by
  let fb (i : Fin (n + 1)) := denoteRegion J M (hb i)
  obtain ⟨c, dc⟩ := collectiveDenotes_exists_succ J M n Γ R L fb
  have den := RegionDenotes.cfg (.br (exitAt R hℓ) ha) hb (.br (h := exitAt R hℓ) dp)
    (fun i => denoteRegion_spec J M (hb i)) dc
  have harg : (J.map p ≫ J.map (labelInject M _ (exitAt R hℓ))) ≫
      J.map (labelAppendSplit M (List.ofFn R) L) =
      (J.map p ≫ J.map (labelInject M ℓ hℓ)) ≫
        J.map (coprod.inl : labelObj M L ⟶ labelObj M L ⨿ labelObj M (List.ofFn R)) := by
    simp only [Category.assoc, ← Functor.map_comp]
    rw [labelAppendSplit_exit M R hℓ]
  rw [harg, case_inl] at den
  have hret : bindArrow J (J.map p ≫ J.map (labelInject M ℓ hℓ))
      (J.map (CartesianMonoidalCategory.snd (ctxObj M Γ) (labelObj M L))) =
      J.map p ≫ J.map (labelInject M ℓ hℓ) := by
    simp only [← Functor.map_comp, Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind,
      extend_map, CartesianMonoidalCategory.lift_snd]
  rw [hret] at den
  exact ⟨_, _, _, den, .br (h := hℓ) dp⟩

theorem cfgBrExit_common {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {ℓ : Nat} {a : Tm Φ}
    {A : τ} {blocks : Fin (n + 1) → Region Φ}
    (R : Fin (n + 1) → τ) (hℓ : At L ℓ A) (ha : Tm.BranchValue Γ a A)
    (hb : ∀ i, Region.HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L)) :
    ∃ (hs : Region.HasType Γ (.cfg (.br (n + 1 + ℓ) a) (n + 1) blocks) L)
      (ht : Region.HasType Γ (.br ℓ a) L), ∃ f, RegionDenotes J M hs f ∧ RegionDenotes J M ht f := by
  obtain ⟨ht, p, dp⟩ := branchValue_denotes J M ha
  exact cfgBrExit_map_common J M R hℓ ht p dp hb

set_option backward.isDefEq.respectTransparency false in
theorem cfgBrLocal_map_common {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {a : Tm Φ}
    {blocks : Fin (n + 1) → Region Φ}
    (R : Fin (n + 1) → τ) (i : Fin (n + 1)) (ha : Tm.HasType Γ a (R i))
    (p : ctxObj M Γ ⟶ M.obj (R i)) (dp : Denotes J M ha (J.map p))
    (hb : ∀ j, Region.HasType (R j :: Γ) (blocks j) (List.ofFn R ++ L)) :
    ∃ (hs : Region.HasType Γ (.cfg (.br i a) (n + 1) blocks) L)
      (ht : Region.HasType Γ (.cfg (.let₁ a (blocks i)) (n + 1) blocks) L),
      ∃ f, RegionDenotes J M hs f ∧ RegionDenotes J M ht f := by
  let fb (j : Fin (n + 1)) := denoteRegion J M (hb j)
  obtain ⟨c, dc⟩ := collectiveDenotes_exists_succ J M n Γ R L fb
  let E := ctxObj M Γ
  let iLocal := labelInject M i (ofFnAt R i)
  let split := J.map (labelAppendSplit M (List.ofFn R) L)
  let body := J.map (𝟙 E ⊗ₘ labelObjToFinite M R) ≫ c ≫ split
  have hout : J.map (labelInject M i (localAt R i L)) ≫ split =
      J.map iLocal ≫ J.map (coprod.inr : labelObj M (List.ofFn R) ⟶
        labelObj M L ⨿ labelObj M (List.ofFn R)) := by
    rw [← J.map_comp, ← J.map_comp, labelAppendSplit_local]
  have hbody : J.map (E ◁ iLocal) ≫ body = fb i ≫ split := by
    dsimp only [body]
    rw [MonoidalCategory.id_tensorHom, ← J.map_comp_assoc,
      ← MonoidalCategory.whiskerLeft_comp, labelObjToFinite_local]
    have h := dc.restrict i
    simpa only [MonoidalCategory.id_tensorHom, Category.assoc] using
      congrArg (· ≫ split) h
  change J.map (ctxObj M Γ ◁ iLocal) ≫ body = fb i ≫ split at hbody
  have db (j : Fin (n + 1)) := denoteRegion_spec J M (hb j)
  have lhs := RegionDenotes.cfg (.br (localAt R i L) ha) hb (.br (h := localAt R i L) dp) db dc
  have rhs := RegionDenotes.cfg (.let₁ ha (hb i)) hb (.let₁ dp (db i)) db dc
  change RegionDenotes J M (.cfg R (.br (localAt R i L) ha) hb)
    (caseWithContext J ((J.map p ≫ J.map (labelInject M i (localAt R i L))) ≫ split)
      (J.map (CartesianMonoidalCategory.snd E (labelObj M L))) (contextualLoop J body)) at lhs
  change RegionDenotes J M (.cfg R (.let₁ ha (hb i)) hb)
    (caseWithContext J (bindArrow J (J.map p) (fb i) ≫ split)
      (J.map (CartesianMonoidalCategory.snd E (labelObj M L))) (contextualLoop J body)) at rhs
  rw [Category.assoc, hout, ← Category.assoc, case_inr] at lhs
  have heq : bindArrow J (J.map p ≫ J.map iLocal) (contextualLoop J body) =
      caseWithContext J (bindArrow J (J.map p) (fb i) ≫ split)
        (J.map (CartesianMonoidalCategory.snd E (labelObj M L))) (contextualLoop J body) := by
    simp only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind,
      extend_post_map, Category.assoc]
    simpa only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind,
      hbody, Category.assoc] using contextualLoop_enter J p iLocal body
  exact ⟨_, _, _, heq ▸ lhs, rhs⟩

theorem cfgBrLocal_common {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {a : Tm Φ}
    {blocks : Fin (n + 1) → Region Φ}
    (R : Fin (n + 1) → τ) (i : Fin (n + 1)) (ha : Tm.BranchValue Γ a (R i))
    (hb : ∀ j, Region.HasType (R j :: Γ) (blocks j) (List.ofFn R ++ L)) :
    ∃ (hs : Region.HasType Γ (.cfg (.br i a) (n + 1) blocks) L)
      (ht : Region.HasType Γ (.cfg (.let₁ a (blocks i)) (n + 1) blocks) L),
      ∃ f, RegionDenotes J M hs f ∧ RegionDenotes J M ht f := by
  obtain ⟨ht, p, dp⟩ := branchValue_denotes J M ha
  exact cfgBrLocal_map_common J M R i ht p dp hb

variable [RegionTypingCoherent (Φ := Φ) J M]

theorem cfgEquiv_common {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : Region.CfgEquiv Γ r s L) :
    ∃ (hr : Region.HasType Γ r L) (hs : Region.HasType Γ s L),
      ∃ f, RegionDenotes J M hr f ∧ RegionDenotes J M hs f := by
  induction h with
  | refl ht =>
      exact ⟨ht, ht, _, denoteRegion_spec J M ht, denoteRegion_spec J M ht⟩
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
          obtain ⟨c, dc⟩ := collectiveDenotes_exists_succ J M n _ R _ fb
          exact ⟨.cfg R he hb, .cfg R he' hb', _,
            .cfg he hb de (fun i => (db i).1) dc, .cfg he' hb' de' (fun i => (db i).2) dc⟩
  | cfgZero he _ =>
      have de := denoteRegion_spec J M he
      exact ⟨.cfg Fin.elim0 he (fun i => i.elim0), he, _, .cfgZero (R := Fin.elim0) he (fun i => i.elim0) de, de⟩
  | cfgBrExit R hl ha hb => exact cfgBrExit_common J M R hl ha hb
  | cfgBrLocal R i ha hb => exact cfgBrLocal_common J M R i ha hb

end Cfg

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
