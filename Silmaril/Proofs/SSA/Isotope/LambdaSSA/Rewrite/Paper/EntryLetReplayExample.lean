module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Replay.Example.Defs

/-! # Fixed representatives at the corrected uniformity boundary -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.EntryLetReplayExample

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithEntryLet.ReplayExample Paper.EntryLetObstruction
open CategoryTheory CategoryTheory.Limits
open Paper.Extension.Singleton (projection projectStep iterateChosen projectSquare_iff coprodComparison_inv_map uniformity_of_split_image)

local notation "J" => projection Seed
local notation "p" => Paper.TypeCategory.ofRegion flatRequest_typed
local notation "q" => Paper.TypeCategory.ofRegion movedRequest_typed

theorem embed_constructor : Paper.TypeCategory.ConstructorReturn embed :=
  ⟨.inl (.var 0), .inl (.var rfl), Paper.TypeCategory.sumCofan_inl U U⟩

private theorem retraction : embed ≫ retract = 𝟙 X := by
  have leg : embed ≫ (Paper.TypeCategory.sumIso U U).hom = (coprod.inl : X ⟶ X ⨿ X) :=
    Paper.TypeCategory.sumCofan_inl_sumIso_hom U U
  rw [retract, ← Category.assoc, leg, coprod.inl_desc]

private theorem left_square :
    source ≫ coprod.map (𝟙 X) embed = p ≫ embed ≫ (coprod.inr : D ⟶ X ⨿ D) := by
  rw [source, Category.assoc, coprod.inr_map]

private theorem right_square :
    embed ≫ target = q ≫ embed ≫ (coprod.inr : D ⟶ X ⨿ D) := by
  rw [target, ← Category.assoc embed retract, retraction, Category.id_comp]

theorem native_square_ne :
    source ≫ coprod.map (𝟙 X) embed ≠ embed ≫ target := by
  rw [left_square, right_square]
  intro eq
  have h := congrArg (fun f : X ⟶ X ⨿ D => f ≫ coprod.desc (𝟙 X) retract) eq
  apply flatRequest_arrow_ne_moved
  simpa only [Category.assoc, coprod.inr_desc, ← Category.assoc embed, retraction, Category.comp_id] using h

theorem corrected_square :
    projectStep Seed source ≫ coprod.map (𝟙 ((J).obj X)) ((J).map embed) =
      (J).map embed ≫ projectStep Seed target := by
  apply (projectSquare_iff Seed source target embed).2
  rw [left_square, right_square, (J).map_comp, (J).map_comp]
  exact congrArg (· ≫ (J).map (embed ≫ (coprod.inr : D ⟶ X ⨿ D))) Paper.WithEntryLet.flatRequest_arrow_eq_moved

theorem native_square_repaired :
    ∃ g : D ⟶ X ⨿ D, projectStep Seed g = projectStep Seed target ∧
      source ≫ coprod.map (𝟙 X) embed = embed ≫ g := by
  refine ⟨retract ≫ p ≫ embed ≫ coprod.inr, ?_, ?_⟩
  · have eq : (J).map p = (J).map q := Paper.WithEntryLet.flatRequest_arrow_eq_moved
    unfold projectStep target
    simp only [Functor.map_comp, eq]
  · rw [← Category.assoc embed retract, retraction, Category.id_comp, left_square]

private theorem native_target_image :
    target ≫ coprod.map (𝟙 X) (retract ≫ embed) = target := by
  simp only [target, Category.assoc, coprod.inr_map]
  rw [← Category.assoc embed retract, retraction, Category.id_comp]

theorem corrected_iterate :
    iterateChosen Seed (projectStep Seed source) =
      (J).map embed ≫ iterateChosen Seed (projectStep Seed target) := by
  have section_id : (J).map embed ≫ (J).map retract = 𝟙 ((J).obj X) := by
    rw [← (J).map_comp, retraction, (J).map_id]
  apply uniformity_of_split_image Seed ((J).map embed) ((J).map retract)
    section_id _ _ corrected_square
  rw [← (J).map_comp, ← (J).map_id X]
  unfold projectStep
  rw [Category.assoc, coprodComparison_inv_map, ← (J).map_comp_assoc, native_target_image]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.EntryLetReplayExample
