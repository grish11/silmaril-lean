module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Tripling.Components.Structural.Payload.Cuts.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Tripling.Components.Structural.Payload.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralTriplingPayloadCuts

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.Extension.Singleton
open Paper.Extension.Singleton.ThreeCycle (fold step triple fold_iff_triple)
open Paper.Extension.Singleton.ThreeCycle.Payload
open Paper.TypeCategory.ComponentTripling (phaseInterleave phaseInterleave_hom phaseInterleave_inv)
open CategoryTheory CategoryTheory.Limits

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "Q" => TypeCategory Seed
local notation "Phases" A:max => (A ⨿ (A ⨿ A))
local notation "I" => iterateChosen Seed

set_option backward.isDefEq.respectTransparency false

private inductive Phase
  | first | middle | last

private noncomputable def phaseIn {A : Q} : Phase → (A ⟶ Phases A)
  | .first => coprod.inl
  | .middle => coprod.inl ≫ coprod.inr
  | .last => coprod.inr ≫ coprod.inr

private theorem enter_right (A D : Q) (i : Phase) :
    phaseIn Seed i ≫ coprod.inr ≫ (phaseInterleave A D).inv =
      coprod.inr ≫ phaseIn Seed i := by
  cases i <;> simp [phaseIn, phaseInterleave_inv]

private theorem phase_out (A D B : Q) (i : Phase) :
    coprod.map (𝟙 B) (phaseIn Seed i) ≫ coprod.map (𝟙 B) (phaseInterleave A D).hom ≫
      (coprod.associator B (Phases A) (Phases D)).inv ≫
      coprod.map (coprod.map (𝟙 B) (fold A)) (𝟙 (Phases D)) =
    (coprod.associator B A D).inv ≫ coprod.map (𝟙 (B ⨿ A)) (phaseIn Seed i) := by
  apply coprod.hom_ext
  · cases i <;> simp [phaseIn, phaseInterleave_hom, coprod.associator]
  · apply coprod.hom_ext <;> cases i <;> simp [phaseIn, phaseInterleave_hom, coprod.associator]

theorem rightRow_eq_step {A D B : Q} (g : A ⨿ D ⟶ B ⨿ (A ⨿ D)) :
    rightRow Seed g = step (targetRightRow Seed g) := by
  have row (i j : Phase) (src : phaseIn Seed i ≫ step g = g ≫ coprod.map (𝟙 B) (phaseIn Seed j))
      (dst : phaseIn Seed i ≫ step (targetRightRow Seed g) =
        targetRightRow Seed g ≫ coprod.map (𝟙 (B ⨿ A)) (phaseIn Seed j)) :
      phaseIn Seed i ≫ rightRow Seed g = phaseIn Seed i ≫ step (targetRightRow Seed g) := by
    let tail := coprod.map (𝟙 B) (phaseInterleave A D).hom ≫
      (coprod.associator B (Phases A) (Phases D)).inv ≫
      coprod.map (coprod.map (𝟙 B) (fold A)) (𝟙 (Phases D))
    calc
      phaseIn Seed i ≫ rightRow Seed g =
          (phaseIn Seed i ≫ coprod.inr ≫ (phaseInterleave A D).inv) ≫ step g ≫ tail := by
        simp only [rightRow, groupedRightRow, groupedRows, tail, Category.assoc]
      _ = coprod.inr ≫ (phaseIn Seed i ≫ step g) ≫ tail := by
        rw [enter_right]
        simp only [Category.assoc]
      _ = phaseIn Seed i ≫ step (targetRightRow Seed g) := by
        rw [src, dst]
        simp only [tail, targetRightRow, Category.assoc, phase_out]
  apply coprod.hom_ext
  · exact row .first .middle (by simp [phaseIn, step]) (by simp [phaseIn, step])
  · apply coprod.hom_ext
    · simpa only [phaseIn, Category.assoc] using
        row .middle .last (by simp [phaseIn, step]) (by simp [phaseIn, step])
    · simpa only [phaseIn, Category.assoc] using
        row .last .first (by simp [phaseIn, step]) (by simp [phaseIn, step])

theorem left_square {A D B : Q} (g : A ⨿ D ⟶ B ⨿ (A ⨿ D))
    (right : I (rightRow Seed g) = fold D ≫ I (targetRightRow Seed g)) :
    leftCut Seed g ≫ coprod.map (𝟙 B) (fold A) = fold A ≫ targetLeftCut Seed g := by
  let over := coprod.map (𝟙 B) (fold A)
  rw [iterate_rightRow] at right
  have ports : coprod.desc (𝟙 (B ⨿ Phases A)) (I (groupedRightRow Seed g)) ≫ over =
      coprod.map over (fold D) ≫ coprod.desc (𝟙 (B ⨿ A)) (I (targetRightRow Seed g)) := by
    rw [coprod.desc_comp, coprod.map_desc, Category.id_comp, Category.comp_id, right]
  rw [leftCut, targetLeftCut, Category.assoc (coprod.inl ≫ groupedRows Seed g), ports,
    ← Category.assoc (coprod.inl ≫ groupedRows Seed g), Category.assoc coprod.inl, rows_square,
    coprod.inl_map_assoc]
  simp only [Category.assoc]

theorem triple_iff_left_uniformity {A D B : Q} (g : A ⨿ D ⟶ B ⨿ (A ⨿ D))
    (right : I (rightRow Seed g) = fold D ≫ I (targetRightRow Seed g)) :
    I (triple g) = I g ↔ I (leftCut Seed g) = fold A ≫ I (targetLeftCut Seed g) := by
  let c := phaseInterleave A D
  let src := groupedRows Seed g ≫ (coprod.associator B (Phases A) (Phases D)).hom
  have coord : step g ≫ coprod.map (𝟙 B) c.hom = c.hom ≫ src := by
    simp only [c, src, groupedRows, Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.hom_inv_id_assoc]
  have src_cut : I src = coprod.desc (I (leftCut Seed g))
      (I (groupedRightRow Seed g) ≫ coprod.desc (𝟙 B) (I (leftCut Seed g))) :=
    iterateChosen_rows Seed (groupedRows Seed g)
  have target_cut : I g = coprod.desc (I (targetLeftCut Seed g))
      (I (targetRightRow Seed g) ≫ coprod.desc (𝟙 B) (I (targetLeftCut Seed g))) := by
    simpa only [targetLeftCut, targetRightRow, Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      (iterateChosen_rows Seed (g ≫ (coprod.associator B A D).inv))
  have group :
      I (step g) = fold (A ⨿ D) ≫ I g ↔
        I src = coprod.map (fold A) (fold D) ≫ I g := by
    rw [uniformity_of_iso Seed c _ _ coord, ← regroup_fold Seed A D]
    change c.hom ≫ I src = (c.hom ≫ coprod.map (fold A) (fold D)) ≫ I g ↔ _
    rw [Category.assoc, cancel_epi]
  rw [← fold_iff_triple Seed g, group, src_cut, target_cut, coprod.map_desc]
  constructor
  · intro h
    simpa using congrArg ((coprod.inl : Phases A ⟶ Phases A ⨿ Phases D) ≫ ·) h
  · intro h
    rw [h]
    have ports : coprod.desc (𝟙 B) (fold A ≫ I (targetLeftCut Seed g)) =
        coprod.map (𝟙 B) (fold A) ≫ coprod.desc (𝟙 B) (I (targetLeftCut Seed g)) := by
      rw [coprod.map_desc, Category.id_comp]
    rw [ports, ← Category.assoc (I (groupedRightRow Seed g)), ← iterate_rightRow, right, Category.assoc]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralTriplingPayloadCuts
