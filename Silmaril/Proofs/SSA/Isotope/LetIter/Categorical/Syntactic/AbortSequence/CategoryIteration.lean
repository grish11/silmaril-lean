module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Iteration.Defs

/-! # Projection and fixpoint for iteration in the LetIter computation quotient -/

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

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.RepairedIterationProofs
