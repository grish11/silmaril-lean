module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Outward.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Combinators
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Labels
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.OutwardEffect

/-! # Factoring a typed case through two local CFG continuations -/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open CategoryTheory CategoryTheory.Limits CategoryTheory.PremonoidalCategory
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (caseWithContext extend splitMapCoprod)
open CategoryTheory.CartesianMonoidalCategory (snd)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]

section Freyd

variable (J : V ⥤ C) [DistributiveFreydCategory J]

private theorem case_snd_desc
    (hu : IsCentral (Functor.StrongPremonoidal.unitIso (J := J)).hom)
    {E A B D : V} (f : J.obj E ⟶ J.obj (A ⨿ B)) (a : A ⟶ D) (b : B ⟶ D) :
    caseWithContext J f (J.map (snd E A ≫ a)) (J.map (snd E B ≫ b)) =
      f ≫ J.map (coprod.desc a b) := by
  let m := DistributiveTensor.leftIso E A B
  let d := J.map m.inv ≫ splitMapCoprod J (E ⊗ A) (E ⊗ B)
  have h : d ≫ coprod.desc (J.map (snd E A ≫ a)) (J.map (snd E B ≫ b)) =
      J.map (snd E (A ⨿ B) ≫ coprod.desc a b) := by
    have : IsIso d := by dsimp [d, splitMapCoprod]; infer_instance
    apply (cancel_epi (inv d)).mp
    apply coprod.hom_ext
    · have hl : (coprod.inl : J.obj (E ⊗ A) ⟶ J.obj (E ⊗ A) ⨿ J.obj (E ⊗ B)) ≫ inv d =
          J.map (E ◁ (coprod.inl : A ⟶ A ⨿ B)) := by
        have he : J.map (E ◁ (coprod.inl : A ⟶ A ⨿ B)) ≫ d = coprod.inl :=
          distributeMap_inl J E A B
        rw [← he, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      simp only [← Category.assoc, hl]
      simp only [Category.assoc, d, m, distributeMap_inl_assoc, coprod.inl_desc, ← J.map_comp,
        CartesianMonoidalCategory.whiskerLeft_snd_assoc, coprod.inl_desc]
    · have hr : (coprod.inr : J.obj (E ⊗ B) ⟶ J.obj (E ⊗ A) ⨿ J.obj (E ⊗ B)) ≫ inv d =
          J.map (E ◁ (coprod.inr : B ⟶ A ⨿ B)) := by
        have he : J.map (E ◁ (coprod.inr : B ⟶ A ⨿ B)) ≫ d = coprod.inr :=
          distributeMap_inr J E A B
        rw [← he, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      simp only [← Category.assoc, hr]
      simp only [Category.assoc, d, m, distributeMap_inr_assoc, coprod.inr_desc, ← J.map_comp,
        CartesianMonoidalCategory.whiskerLeft_snd_assoc, coprod.inr_desc]
  have hd : J.map m.inv ≫ splitMapCoprod J (E ⊗ A) (E ⊗ B) ≫
      coprod.desc (J.map (snd E A ≫ a)) (J.map (snd E B ≫ b)) =
      J.map (snd E (A ⨿ B) ≫ coprod.desc a b) := by
    simpa only [d, Category.assoc] using h
  simp only [caseWithContext, Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind]
  rw [hd, J.map_comp, ← Category.assoc, extend_snd J hu]

end Freyd

section Region

variable [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]

set_option backward.isDefEq.respectTransparency false in
theorem caseCfg_common (hu : IsCentral (Functor.StrongPremonoidal.unitIso (J := J)).hom)
    {Γ : VCtx τ} {L : LCtx τ} {e : Tm Φ} {A B : τ} {l r : Region Φ}
    (he : Tm.HasType Γ e (Silmaril.coprod A B))
    (hl : Region.HasType (A :: Γ) l L) (hr : Region.HasType (B :: Γ) r L) :
    ∃ ht : Region.HasType Γ
      (.cfg (.case e (.br 0 (.var 0)) (.br 1 (.var 0))) 2
        (fun i => Region.renameLabels (fun j => 2 + j) (Fin.cases l (fun _ => r) i))) L,
      ∃ f, RegionDenotes J M (.case he hl hr) f ∧ RegionDenotes J M ht f := by
  obtain ⟨fe, de⟩ := denotes_exists J M he
  obtain ⟨fl, dl⟩ := regionDenotes_exists J M hl
  obtain ⟨fr, dr⟩ := regionDenotes_exists J M hr
  let E := ctxObj M Γ
  change J.obj (E ⊗ M.obj A) ⟶ J.obj (labelObj M L) at fl
  change J.obj (E ⊗ M.obj B) ⟶ J.obj (labelObj M L) at fr
  let R : Fin 2 → τ := Fin.cases A (fun _ => B)
  let blocks : Fin 2 → Region Φ := Fin.cases l (fun _ => r)
  let hblocks : ∀ i, Region.HasType (R i :: Γ) (blocks i) L :=
    Fin.cases hl (fun _ => hr)
  let fb : ∀ i, J.obj (ctxObj M (R i :: Γ)) ⟶ J.obj (labelObj M L) :=
    Fin.cases fl (fun _ => fr)
  have db : ∀ i, RegionDenotes J M (hblocks i) (fb i) := Fin.cases dl (fun _ => dr)
  let h0 : At (List.ofFn R) 0 A := ofFnAt R (0 : Fin 2)
  let h1 : At (List.ofFn R) 1 B := ofFnAt R (1 : Fin 2)
  let j0 : M.obj A ⟶ labelObj M (List.ofFn R) := labelInject M 0 h0
  let j1 : M.obj B ⟶ labelObj M (List.ofFn R) := labelInject M 1 h1
  let f := fe ≫ J.map (M.coprodIso A B).hom
  have dh := RegionDenotes.case de (RegionDenotes.br (h := h0) (Denotes.var (i := 0) rfl))
    (RegionDenotes.br (h := h1) (Denotes.var (i := 0) rfl))
  change RegionDenotes J M _
    (caseWithContext J f (J.map (snd E (M.obj A)) ≫ J.map j0)
      (J.map (snd E (M.obj B)) ≫ J.map j1)) at dh
  rw [← J.map_comp, ← J.map_comp, case_snd_desc J hu] at dh
  let q : finiteLabelObj M R ⟶ M.obj A ⨿ M.obj B :=
    Limits.Sigma.desc (Fin.cases coprod.inl (fun _ => coprod.inr))
  have q0 : finiteLabelInject M R 0 ≫ q = coprod.inl := Limits.Sigma.ι_comp_desc _ _
  have q1 : finiteLabelInject M R 1 ≫ q = coprod.inr := Limits.Sigma.ι_comp_desc _ _
  let route := J.map (DistributiveTensor.leftIso E (M.obj A) (M.obj B)).inv ≫
    splitMapCoprod J (E ⊗ M.obj A) (E ⊗ M.obj B) ≫ coprod.desc fl fr
  let g := J.map (E ◁ q) ≫ route
  have hg : ∀ i, J.map (E ◁ finiteLabelInject M R i) ≫ g = fb i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change J.map (E ◁ finiteLabelInject M R 0) ≫ J.map (E ◁ q) ≫ route = fl
      rw [← J.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp, q0]
      change J.map (E ◁ (coprod.inl : M.obj A ⟶ M.obj A ⨿ M.obj B)) ≫ route = fl
      simp only [route, distributeMap_inl_assoc, coprod.inl_desc]
    · obtain rfl := Fin.eq_zero j
      change J.map (E ◁ finiteLabelInject M R 1) ≫ J.map (E ◁ q) ≫ route = fr
      rw [← J.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp, q1]
      change J.map (E ◁ (coprod.inr : M.obj B ⟶ M.obj A ⨿ M.obj B)) ≫ route = fr
      simp only [route, distributeMap_inr_assoc, coprod.inr_desc]
  obtain ⟨ht, dg⟩ := cfgLink_common J M hu R _ hblocks dh db g hg
  have heq : coprod.desc j0 j1 ≫ labelObjToFinite M R ≫ q = 𝟙 _ := by
    apply coprod.hom_ext
    · rw [coprod.inl_desc_assoc, Category.comp_id]
      change labelInject M (0 : Fin 2) h0 ≫ labelObjToFinite M R ≫ q = _
      rw [← Category.assoc, labelObjToFinite_local M R 0 h0, q0]
      rfl
    · rw [coprod.inr_desc_assoc, Category.comp_id]
      change labelInject M (1 : Fin 2) h1 ≫ labelObjToFinite M R ≫ q = _
      rw [← Category.assoc, labelObjToFinite_local M R 1 h1, q1]
      rfl
  have e : extend J (f ≫ J.map (coprod.desc j0 j1)) ≫
      J.map (E ◁ labelObjToFinite M R) ≫ g = caseWithContext J f fl fr := by
    rw [extend_post_map J]
    simp only [Category.assoc]
    change extend J f ≫ J.map (E ◁ coprod.desc j0 j1) ≫
      J.map (E ◁ labelObjToFinite M R) ≫ J.map (E ◁ q) ≫ route = _
    rw [← J.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp, ← J.map_comp_assoc,
      ← MonoidalCategory.whiskerLeft_comp, Category.assoc, heq, MonoidalCategory.whiskerLeft_id,
      J.map_id, Category.id_comp]
    rfl
  rw [e] at dg
  exact ⟨ht, _, RegionDenotes.case de dl dr, dg⟩

end Region

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
