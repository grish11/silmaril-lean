module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Iteration.Defs

/-! # Projection and Elgot equations for iteration in the LetIter computation quotient -/

public section

universe u

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.RepairedIterationProofs

open CategoryTheory CategoryTheory.Limits
open Silmaril.Thesis.LambdaIter.Syn (SynCat)

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]

variable (pe : ε)

local notation "S" => signature (τ := τ) (Φ := Φ) pe
local notation "P" => repairedProjection (τ := τ) (Φ := Φ) pe

theorem repairedIteration_map {X Y : SynCat S} (f : X ⟶ Y ⨿ X) :
    CategoryTheory.iterate ((P).map f ≫ (repairedProjectionCoprodIso pe Y X).hom) =
      (P).map (CategoryTheory.iterate f) := by
  change (P).map (CategoryTheory.iterate
    ((P).preimage (((P).map f ≫ (repairedProjectionCoprodIso pe Y X).hom) ≫
      (repairedProjectionCoprodIso pe Y X).inv))) = _
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply (repairedProjection_map_eq_iff pe _ _).mpr
  apply repairedHomClass_iterate_congr pe
  exact (repairedProjection_map_eq_iff pe _ _).mp ((P).map_preimage ((P).map f))

theorem repairedProjection_coprodIso_desc {X Y Z : SynCat S} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (repairedProjectionCoprodIso pe X Y).hom ≫ coprod.desc ((P).map f) ((P).map g) =
      (P).map (coprod.desc f g) := by
  apply repairedProjection_coprod_hom_ext pe
  · rw [← Category.assoc, repairedProjection_coprodIso_inl, coprod.inl_desc,
      ← (P).map_comp, coprod.inl_desc]
  · rw [← Category.assoc, repairedProjection_coprodIso_inr, coprod.inr_desc,
      ← (P).map_comp, coprod.inr_desc]

theorem repairedIteration_body_surjective {X Y : RepairedSynCat (τ := τ) (Φ := Φ) pe}
    (f : X ⟶ Y ⨿ X) :
    ∃ g : X.as ⟶ Y.as ⨿ X.as, (P).map g ≫ (repairedProjectionCoprodIso pe Y.as X.as).hom = f := by
  obtain ⟨g, hg⟩ := (P).map_surjective (f ≫ (repairedProjectionCoprodIso pe Y.as X.as).inv)
  exact ⟨g, by rw [hg, Category.assoc, Iso.inv_hom_id, Category.comp_id]⟩

theorem repairedIteration_fixpoint {X Y : RepairedSynCat (τ := τ) (Φ := Φ) pe}
    (f : X ⟶ Y ⨿ X) :
    CategoryTheory.iterate f = f ≫ coprod.desc (𝟙 Y) (CategoryTheory.iterate f) := by
  obtain ⟨g, rfl⟩ := repairedIteration_body_surjective pe f
  have hId : 𝟙 Y = (P).map (𝟙 Y.as) := ((P).map_id Y.as).symm
  rw [repairedIteration_map, Category.assoc, hId,
    repairedProjection_coprodIso_desc, ← (P).map_comp, ← ElgotCategory.fixpoint]

private theorem repairedProjection_coprodIso_map {X Y U V : SynCat S} (f : X ⟶ U) (g : Y ⟶ V) :
    (repairedProjectionCoprodIso pe X Y).hom ≫ coprod.map ((P).map f) ((P).map g) =
      (P).map (coprod.map f g) ≫ (repairedProjectionCoprodIso pe U V).hom := by
  apply repairedProjection_coprod_hom_ext pe
  · rw [← Category.assoc, repairedProjection_coprodIso_inl, coprod.inl_map]
    rw [← Category.assoc, ← (P).map_comp, coprod.inl_map, (P).map_comp,
      Category.assoc, repairedProjection_coprodIso_inl]
  · rw [← Category.assoc, repairedProjection_coprodIso_inr, coprod.inr_map]
    rw [← Category.assoc, ← (P).map_comp, coprod.inr_map, (P).map_comp,
      Category.assoc, repairedProjection_coprodIso_inr]


theorem repairedIteration_naturality {X Y Z : RepairedSynCat (τ := τ) (Φ := Φ) pe}
    (f : X ⟶ Y ⨿ X) (g : Y ⟶ Z) :
    CategoryTheory.iterate f ≫ g =
      CategoryTheory.iterate (f ≫ coprod.map g (𝟙 X)) := by
  obtain ⟨f, rfl⟩ := repairedIteration_body_surjective pe f
  obtain ⟨g, rfl⟩ := (P).map_surjective (X := Y.as) (Y := Z.as) g
  have hId : 𝟙 X = (P).map (𝟙 X.as) := ((P).map_id X.as).symm
  rw [repairedIteration_map, hId, Category.assoc, repairedProjection_coprodIso_map,
    ← Category.assoc]
  simp only [← Functor.map_comp, repairedIteration_map, ElgotCategory.naturality]


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem repairedIteration_codiagonal {X Y : RepairedSynCat (τ := τ) (Φ := Φ) pe}
    (f : X ⟶ (Y ⨿ X) ⨿ X) :
    CategoryTheory.iterate (CategoryTheory.iterate f) =
      CategoryTheory.iterate (f ≫ coprod.desc (𝟙 (Y ⨿ X)) (coprod.inr : X ⟶ Y ⨿ X)) := by
  let inner := repairedProjectionCoprodIso pe Y.as X.as
  let outer := repairedProjectionCoprodIso pe (Y.as ⨿ X.as) X.as
  let comparison := outer.trans (coprod.mapIso inner (Iso.refl X))
  obtain ⟨g, hg⟩ := (P).map_surjective (f ≫ comparison.inv)
  have f_rep : (P).map g ≫ outer.hom ≫ coprod.map inner.hom (𝟙 X) = f := by
    change (P).map g ≫ comparison.hom = f
    rw [hg, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have step : CategoryTheory.iterate f = (P).map (CategoryTheory.iterate g) ≫ inner.hom := by
    rw [← f_rep, ← Category.assoc, ← repairedIteration_naturality, repairedIteration_map]
  have hdesc : coprod.map inner.hom (𝟙 X) ≫
        coprod.desc (𝟙 (Y ⨿ X)) (coprod.inr : X ⟶ Y ⨿ X) =
        coprod.desc ((P).map (𝟙 (Y.as ⨿ X.as)))
          ((P).map (coprod.inr : X.as ⟶ Y.as ⨿ X.as)) ≫ inner.hom := by
    have hom_id : inner.hom ≫ 𝟙 (Y ⨿ X) = inner.hom := Category.comp_id _
    have inr_comparison :
        (P).map (coprod.inr : X.as ⟶ Y.as ⨿ X.as) ≫ inner.hom = (coprod.inr : X ⟶ Y ⨿ X) :=
      repairedProjection_coprodIso_inr pe Y.as X.as
    simp only [coprod.map_desc, coprod.desc_comp, (P).map_id, Category.id_comp, hom_id, inr_comparison]
    rfl
  have foldBody : f ≫ coprod.desc (𝟙 (Y ⨿ X)) (coprod.inr : X ⟶ Y ⨿ X) =
      (P).map (g ≫ coprod.desc (𝟙 (Y.as ⨿ X.as)) (coprod.inr : X.as ⟶ Y.as ⨿ X.as)) ≫ inner.hom := by
    have outer_desc :
        outer.hom ≫ coprod.desc ((P).map (𝟙 (Y.as ⨿ X.as)))
            ((P).map (coprod.inr : X.as ⟶ Y.as ⨿ X.as)) =
          (P).map (coprod.desc (𝟙 (Y.as ⨿ X.as)) (coprod.inr : X.as ⟶ Y.as ⨿ X.as)) :=
      repairedProjection_coprodIso_desc pe _ _
    let exit := coprod.desc ((P).map (𝟙 (Y.as ⨿ X.as)))
      ((P).map (coprod.inr : X.as ⟶ Y.as ⨿ X.as))
    calc
      _ = (P).map g ≫ outer.hom ≫ (coprod.map inner.hom (𝟙 X) ≫
          coprod.desc (𝟙 (Y ⨿ X)) (coprod.inr : X ⟶ Y ⨿ X)) := by
        rw [← f_rep, Category.assoc, Category.assoc]
        rfl
      _ = (P).map g ≫ outer.hom ≫ (exit ≫ inner.hom) :=
        congrArg (fun arrow => (P).map g ≫ outer.hom ≫ arrow) hdesc
      _ = ((P).map g ≫ (outer.hom ≫ exit)) ≫ inner.hom := by simp only [Category.assoc]
      _ = _ := by
        dsimp only [exit]
        rw [outer_desc, ← (P).map_comp]
  rw [step, foldBody]
  change CategoryTheory.iterate ((P).map (CategoryTheory.iterate g) ≫
    (repairedProjectionCoprodIso pe Y.as X.as).hom) =
      CategoryTheory.iterate ((P).map (g ≫ coprod.desc (𝟙 (Y.as ⨿ X.as)) coprod.inr) ≫
        (repairedProjectionCoprodIso pe Y.as X.as).hom)
  rw [repairedIteration_map, repairedIteration_map, ElgotCategory.codiagonal]

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.RepairedIterationProofs
