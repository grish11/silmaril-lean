module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Laws.Thms

/-! # Elimination of a chosen recursive summand -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ChosenBlockFeedback

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.Extension.Singleton

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "Q" => TypeCategory Seed
local notation "I" => iterateChosen Seed

theorem iterate_restrict {X D B : Q} (i : D ⟶ X) (a : X ⟶ B ⨿ D) :
    i ≫ I (a ≫ coprod.map (𝟙 B) i) = I (i ≫ a) := by
  rw [iterateChosen_roll Seed a (coprod.map (𝟙 B) i), coprod.map_map, Category.id_comp]
  have e := iterateChosen_roll Seed (i ≫ a) (𝟙 (B ⨿ D))
  simpa only [Category.comp_id, Category.id_comp, Category.assoc] using e.symm

set_option hygiene false in
set_option quotPrecheck false in
local notation "l" => (coprod.inl : A ⟶ A ⨿ D)
set_option hygiene false in
set_option quotPrecheck false in
local notation "r" => (coprod.inr : D ⟶ A ⨿ D)
set_option hygiene false in
set_option quotPrecheck false in
local notation "assocSum" => (coprod.associator B A D)
set_option hygiene false in
set_option quotPrecheck false in
local notation "embed" => coprod.map (𝟙 B) l

private noncomputable def cut {A D B : Q} (d : A ⨿ D ⟶ (B ⨿ A) ⨿ D) :
    A ⨿ D ⟶ (B ⨿ (A ⨿ D)) ⨿ (A ⨿ D) :=
  d ≫ coprod.map (embed) r

private theorem cut_flatten {A D B : Q} (d : A ⨿ D ⟶ (B ⨿ A) ⨿ D) :
    cut Seed d ≫ coprod.desc (𝟙 (B ⨿ (A ⨿ D))) (coprod.inr : A ⨿ D ⟶ B ⨿ (A ⨿ D)) =
      d ≫ (assocSum).hom := by
  rw [cut, Category.assoc]
  congr 1
  apply coprod.hom_ext
  · simp [coprod.associator]
    apply coprod.hom_ext <;> simp
  · simp [coprod.associator]

private theorem cut_right {A D B : Q} (d : A ⨿ D ⟶ (B ⨿ A) ⨿ D) :
    r ≫ I (cut Seed d) = I (r ≫ d) ≫ embed := by
  let a : A ⨿ D ⟶ (B ⨿ (A ⨿ D)) ⨿ D := d ≫ coprod.map (embed) (𝟙 D)
  have ha : cut Seed d = a ≫ coprod.map (𝟙 (B ⨿ (A ⨿ D))) r := by
    simp only [cut, a, Category.assoc, coprod.map_map, Category.comp_id, Category.id_comp]
  rw [ha, iterate_restrict]
  change I (r ≫ d ≫ coprod.map (embed) (𝟙 D)) = _
  rw [← Category.assoc, ← iterateChosen_naturality]

private noncomputable def eliminateRight {A D B : Q} (d : A ⨿ D ⟶ (B ⨿ A) ⨿ D) : A ⨿ D ⟶ B ⨿ A :=
  d ≫ coprod.desc (𝟙 (B ⨿ A)) (I (r ≫ d))

private theorem cut_iterate {A D B : Q} (d : A ⨿ D ⟶ (B ⨿ A) ⨿ D) :
    I (cut Seed d) = eliminateRight Seed d ≫ embed := by
  calc
    I (cut Seed d) = cut Seed d ≫ coprod.desc (𝟙 _) (I (cut Seed d)) :=
      iterateChosen_fixpoint Seed _
    _ = eliminateRight Seed d ≫ embed := by
      rw [show cut Seed d = d ≫ coprod.map (embed) r from rfl]
      rw [Category.assoc, coprod.map_desc, Category.comp_id]
      change d ≫ coprod.desc (embed) (r ≫ I (cut Seed d)) = _
      rw [cut_right, eliminateRight, Category.assoc, coprod.desc_comp, Category.id_comp]

theorem iterate_rows {A D B : Q} (d : A ⨿ D ⟶ (B ⨿ A) ⨿ D) :
    let right := I (r ≫ d)
    let left := I ((l ≫ d) ≫ coprod.desc (𝟙 (B ⨿ A)) right)
    I (d ≫ (assocSum).hom) = coprod.desc left (right ≫ coprod.desc (𝟙 B) left) := by
  rw [← cut_flatten Seed d, ← iterateChosen_codiagonal, cut_iterate]
  have leftEq : l ≫ I (eliminateRight Seed d ≫ embed) = I (l ≫ eliminateRight Seed d) :=
    iterate_restrict Seed l _
  have rightEq : r ≫ eliminateRight Seed d = I (r ≫ d) := by
    rw [eliminateRight, ← Category.assoc, ← iterateChosen_fixpoint Seed (r ≫ d)]
  have leftBody : l ≫ eliminateRight Seed d = (l ≫ d) ≫ coprod.desc (𝟙 (B ⨿ A)) (I (r ≫ d)) := by
    rw [eliminateRight, Category.assoc]
  apply coprod.hom_ext
  · rw [coprod.inl_desc, leftEq, leftBody]
  · conv_lhs => rw [iterateChosen_fixpoint Seed (eliminateRight Seed d ≫ embed)]
    simp only [Category.assoc, coprod.map_desc, Category.id_comp]
    rw [← Category.assoc r, rightEq, leftEq, leftBody, coprod.inr_desc]
    rw [Category.assoc]

theorem iterate_bypass {S R B : Q} (first : S ⟶ (B ⨿ S) ⨿ R) (second : R ⟶ B ⨿ S) :
    iterateChosen Seed (first ≫ coprod.desc (𝟙 (B ⨿ S)) second) =
      coprod.inl ≫ iterateChosen Seed
        (coprod.desc first (second ≫ coprod.inl) ≫ (coprod.associator B S R).hom) := by
  rw [iterate_rows]
  simp only [coprod.inl_desc, coprod.inr_desc]
  have exit : iterateChosen Seed (second ≫ (coprod.inl : B ⨿ S ⟶ (B ⨿ S) ⨿ R)) = second := by
    conv_lhs => rw [iterateChosen_fixpoint Seed]
    simp
  rw [exit]

theorem block_square_iff {A D E B : Q} (h : D ⟶ E)
    (d : A ⨿ D ⟶ (B ⨿ A) ⨿ D) (e : A ⨿ E ⟶ (B ⨿ A) ⨿ E) :
    (d ≫ (coprod.associator B A D).hom) ≫ coprod.map (𝟙 B) (coprod.map (𝟙 A) h) =
        coprod.map (𝟙 A) h ≫ e ≫ (coprod.associator B A E).hom ↔
      d ≫ coprod.map (𝟙 (B ⨿ A)) h = coprod.map (𝟙 A) h ≫ e := by
  have natural : (coprod.associator B A D).hom ≫ coprod.map (𝟙 B) (coprod.map (𝟙 A) h) =
      coprod.map (𝟙 (B ⨿ A)) h ≫ (coprod.associator B A E).hom := by
    apply coprod.hom_ext
    · apply coprod.hom_ext <;> simp [coprod.associator]
    · simp [coprod.associator]
  rw [Category.assoc, natural, ← Category.assoc d, ← Category.assoc (coprod.map (𝟙 A) h), cancel_mono]

theorem iterate_of_right_block {A D E B : Q} (h : D ⟶ E)
    (d : A ⨿ D ⟶ (B ⨿ A) ⨿ D) (e : A ⨿ E ⟶ (B ⨿ A) ⨿ E)
    (square : d ≫ coprod.map (𝟙 (B ⨿ A)) h = coprod.map (𝟙 A) h ≫ e)
    (inner : I (coprod.inr ≫ d) = h ≫ I (coprod.inr ≫ e)) :
    I (d ≫ (coprod.associator B A D).hom) =
      coprod.map (𝟙 A) h ≫ I (e ≫ (coprod.associator B A E).hom) := by
  have row : ((coprod.inl : A ⟶ A ⨿ D) ≫ d) ≫ coprod.map (𝟙 (B ⨿ A)) h = coprod.inl ≫ e := by
    rw [Category.assoc, square, coprod.inl_map_assoc, Category.id_comp]
  have outer :
      (coprod.inl ≫ d) ≫ coprod.desc (𝟙 (B ⨿ A)) (I (coprod.inr ≫ d)) =
        (coprod.inl ≫ e) ≫ coprod.desc (𝟙 (B ⨿ A)) (I (coprod.inr ≫ e)) := by
    rw [inner, ← row, Category.assoc (coprod.inl ≫ d), coprod.map_desc, Category.id_comp]
  rw [iterate_rows Seed d, iterate_rows Seed e]
  rw [outer, inner]
  simp only [coprod.map_desc, Category.id_comp, Category.assoc]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ChosenBlockFeedback
