module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Blocks.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Uniformity.Thms

/-! # Native doubling for two switching rows -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SwitchingDoubling

open Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {X Y B : τ}

local notation "Obj" => ofType (Φ := Φ)
local notation "S" => Obj (Silmaril.coprod X Y)

set_option backward.isDefEq.respectTransparency false

theorem switching_double_rows (g : S ⟶ Obj B ⨿ S)
    (left : Obj X ⟶ Obj B ⨿ Obj Y) (right : Obj Y ⟶ Obj B ⨿ Obj X)
    (hl : (sumCofan X Y).inl ≫ g = left ≫ coprod.map (𝟙 (Obj B)) (sumCofan X Y).inr)
    (hr : (sumCofan X Y).inr ≫ g = right ≫ coprod.map (𝟙 (Obj B)) (sumCofan X Y).inl) :
    let doubled := g ≫ coprod.desc coprod.inl g
    (sumCofan X Y).inl ≫ doubled =
      (left ≫ coprod.desc coprod.inl right) ≫ coprod.map (𝟙 (Obj B)) (sumCofan X Y).inl ∧
    (sumCofan X Y).inr ≫ doubled =
      (right ≫ coprod.desc coprod.inl left) ≫ coprod.map (𝟙 (Obj B)) (sumCofan X Y).inr := by
  dsimp only
  let i : Obj X ⟶ S := (sumCofan X Y).inl
  let j : Obj Y ⟶ S := (sumCofan X Y).inr
  constructor
  · change i ≫ (g ≫ coprod.desc coprod.inl g) =
      (left ≫ coprod.desc coprod.inl right) ≫ coprod.map (𝟙 (Obj B)) i
    rw [← Category.assoc i, show i ≫ g = left ≫ coprod.map (𝟙 (Obj B)) j from hl]
    simp only [Category.assoc, coprod.map_desc, Category.id_comp, coprod.desc_comp, coprod.inl_map,
      show j ≫ g = right ≫ coprod.map (𝟙 (Obj B)) i from hr]
  · change j ≫ (g ≫ coprod.desc coprod.inl g) =
      (right ≫ coprod.desc coprod.inl left) ≫ coprod.map (𝟙 (Obj B)) j
    rw [← Category.assoc j, show j ≫ g = right ≫ coprod.map (𝟙 (Obj B)) i from hr]
    simp only [Category.assoc, coprod.map_desc, Category.id_comp, coprod.desc_comp, coprod.inl_map,
      show i ≫ g = left ≫ coprod.map (𝟙 (Obj B)) j from hl]

theorem iterate_double_of_switching_rows_with_exit (g : S ⟶ Obj B ⨿ S)
    (left : Obj X ⟶ Obj B ⨿ Obj Y) (right : Obj Y ⟶ Obj B ⨿ Obj X)
    (hl : (sumCofan X Y).inl ≫ g = left ≫ coprod.map (𝟙 (Obj B)) (sumCofan X Y).inr)
    (hr : (sumCofan X Y).inr ≫ g = right ≫ coprod.map (𝟙 (Obj B)) (sumCofan X Y).inl) :
    iterate (g ≫ coprod.desc coprod.inl g) = iterate g := by
  let i : Obj X ⟶ S := (sumCofan X Y).inl
  let j : Obj Y ⟶ S := (sumCofan X Y).inr
  let leftRow : Obj X ⟶ (Obj B ⨿ Obj X) ⨿ Obj Y := left ≫ coprod.map coprod.inl (𝟙 (Obj Y))
  let rightRow : Obj Y ⟶ (Obj B ⨿ Obj X) ⨿ Obj Y := right ≫ coprod.inl
  let leftLoop := left ≫ coprod.desc coprod.inl right
  let rightLoop := right ≫ coprod.desc coprod.inl left
  let doubled : S ⟶ Obj B ⨿ S := g ≫ coprod.desc coprod.inl g
  have joined : blockCopair leftRow rightRow ≫ joinBlockExits X Y (Obj B) = g := by
    apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit X Y)
    · change i ≫ (blockCopair leftRow rightRow ≫ joinBlockExits X Y (Obj B)) = i ≫ g
      rw [← Category.assoc i, show i ≫ blockCopair leftRow rightRow = leftRow from inl_blockCopair _ _,
        show i ≫ g = left ≫ coprod.map (𝟙 (Obj B)) j from hl]
      unfold leftRow joinBlockExits
      simp only [Category.assoc, coprod.map_desc, Category.id_comp, coprod.inl_map]
      congr 1
      apply coprod.hom_ext
      · simp
      · simp [j]
        rfl
    · change j ≫ (blockCopair leftRow rightRow ≫ joinBlockExits X Y (Obj B)) = j ≫ g
      rw [← Category.assoc j, show j ≫ blockCopair leftRow rightRow = rightRow from inr_blockCopair _ _,
        show j ≫ g = right ≫ coprod.map (𝟙 (Obj B)) i from hr]
      simp only [rightRow, joinBlockExits, Category.assoc, coprod.inl_desc]
      rfl
  have exitRight : iterate rightRow = right := by
    calc
      _ = rightRow ≫ coprod.desc (𝟙 _) (iterate rightRow) := iterate_fixpoint rightRow
      _ = _ := by simp [rightRow, Category.assoc]
  have nested : leftRow ≫ coprod.desc (𝟙 (Obj B ⨿ Obj X)) (iterate rightRow) = leftLoop := by
    rw [exitRight]
    simp only [leftRow, leftLoop, Category.assoc, coprod.map_desc, Category.comp_id, Category.id_comp]
  have single : iterate g = blockCopair (iterate leftLoop) (right ≫ coprod.desc (𝟙 _) (iterate leftLoop)) := by
    have eq := iterate_join_blocks X Y (Obj B) leftRow rightRow
    dsimp only at eq
    rw [joined, nested, exitRight] at eq
    exact eq
  have rotate : iterate rightLoop = right ≫ coprod.desc (𝟙 (Obj B)) (iterate leftLoop) :=
    iterate_dinaturality right left
  have rows := switching_double_rows g left right hl hr
  have ic : ConstructorReturn i := ⟨_, .inl (.var (i := 0) rfl), sumCofan_inl X Y⟩
  have jc : ConstructorReturn j := ⟨_, .inr (.var (i := 0) rfl), sumCofan_inr X Y⟩
  change iterate doubled = iterate g
  apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit X Y)
  · change i ≫ iterate doubled = i ≫ iterate g
    rw [← iterate_uniformity_ofConstructorReturn ic leftLoop doubled rows.1.symm, single]
    exact (inl_blockCopair _ _).symm
  · change j ≫ iterate doubled = j ≫ iterate g
    rw [← iterate_uniformity_ofConstructorReturn jc rightLoop doubled rows.2.symm, rotate, single]
    exact (inr_blockCopair _ _).symm

theorem iterate_double_of_switching_rows (g : S ⟶ Obj B ⨿ S)
    (left : Obj X ⟶ Obj Y) (right : Obj Y ⟶ Obj X)
    (hl : (sumCofan X Y).inl ≫ g = left ≫ (sumCofan X Y).inr ≫ coprod.inr)
    (hr : (sumCofan X Y).inr ≫ g = right ≫ (sumCofan X Y).inl ≫ coprod.inr) :
    iterate (g ≫ coprod.desc coprod.inl g) = iterate g := by
  apply iterate_double_of_switching_rows_with_exit g
    (left ≫ (coprod.inr : Obj Y ⟶ Obj B ⨿ Obj Y))
    (right ≫ (coprod.inr : Obj X ⟶ Obj B ⨿ Obj X))
  · rw [hl]
    simp only [Category.assoc, coprod.inr_map]
  · rw [hr]
    simp only [Category.assoc, coprod.inr_map]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SwitchingDoubling
