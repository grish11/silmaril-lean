module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Doubling.Switching.OneSided.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Uniformity.Thms

/-! # Exact native elimination at the single and doubled endpoints -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OneSidedDoubling

open Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
open Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.OneSidedSwitch
open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {X Y B : τ}

local notation "Obj" => ofType (Φ := Φ)
local notation "S" => Obj (Silmaril.coprod X Y)
local notation "Exit" => Obj B
local notation "Ports" => (Exit ⨿ Obj X) ⨿ Obj Y

set_option backward.isDefEq.respectTransparency false

theorem doubled_eq (left : Obj X ⟶ Ports) (right : Obj Y ⟶ Exit ⨿ Obj X) :
    step left right ≫ coprod.desc coprod.inl (step left right) =
      blockCopair (doubledLeft left right) (doubledRight left right) ≫ joinBlockExits X Y Exit := by
  let join := joinBlockExits X Y Exit
  let next := coprod.desc coprod.inl (step left right)
  let i : Obj X ⟶ S := (sumCofan X Y).inl
  let j : Obj Y ⟶ S := (sumCofan X Y).inr
  have hl : i ≫ step left right = left ≫ join := by
    change i ≫ (blockCopair left (right ≫ coprod.inl) ≫ join) = _
    rw [← Category.assoc i, show i ≫ blockCopair left (right ≫ coprod.inl) = left from inl_blockCopair _ _]
  have hr : j ≫ step left right = right ≫ coprod.inl ≫ join := by
    change j ≫ (blockCopair left (right ≫ coprod.inl) ≫ join) = _
    rw [← Category.assoc j,
      show j ≫ blockCopair left (right ≫ coprod.inl) = right ≫ coprod.inl from inr_blockCopair _ _,
      Category.assoc]
  have enterLeft : (coprod.inl : Exit ⨿ Obj X ⟶ Ports) ≫ join = coprod.map (𝟙 Exit) i := by
    unfold join joinBlockExits
    exact coprod.inl_desc _ _
  have enterRight : (coprod.inr : Obj Y ⟶ Ports) ≫ join = j ≫ coprod.inr := by
    unfold join joinBlockExits
    exact coprod.inr_desc _ _
  have exitLeft : (coprod.inl : Exit ⟶ Exit ⨿ Obj X) ≫ coprod.inl ≫ join =
      (coprod.inl : Exit ⟶ Exit ⨿ S) := by
    rw [enterLeft, coprod.inl_map, Category.id_comp]
  let dispatchRows := coprod.desc (afterLeft left) (right ≫ coprod.inl)
  have dispatch : join ≫ next = dispatchRows ≫ join := by
    apply coprod.hom_ext
    · have row : (coprod.inl : Exit ⨿ Obj X ⟶ Ports) ≫ dispatchRows = afterLeft left := coprod.inl_desc _ _
      rw [← Category.assoc coprod.inl join, enterLeft, ← Category.assoc coprod.inl dispatchRows, row]
      unfold next afterLeft
      rw [coprod.map_desc, Category.id_comp, hl, coprod.desc_comp, Category.assoc, exitLeft]
    · have row : (coprod.inr : Obj Y ⟶ Ports) ≫ dispatchRows = right ≫ coprod.inl := coprod.inr_desc _ _
      rw [← Category.assoc coprod.inr join, enterRight, ← Category.assoc coprod.inr dispatchRows, row]
      unfold next
      rw [Category.assoc, coprod.inr_desc, hr, Category.assoc]
  change (blockCopair left (right ≫ coprod.inl) ≫ join) ≫ next = _
  rw [Category.assoc, dispatch]
  apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit X Y)
  · change i ≫ (blockCopair left (right ≫ coprod.inl) ≫ dispatchRows ≫ join) =
      i ≫ (blockCopair (doubledLeft left right) (doubledRight left right) ≫ join)
    rw [← Category.assoc i, show i ≫ blockCopair left (right ≫ coprod.inl) = left from inl_blockCopair _ _,
      ← Category.assoc i,
      show i ≫ blockCopair (doubledLeft left right) (doubledRight left right) =
        doubledLeft left right from inl_blockCopair _ _, doubledLeft, Category.assoc]
  · change j ≫ (blockCopair left (right ≫ coprod.inl) ≫ dispatchRows ≫ join) =
      j ≫ (blockCopair (doubledLeft left right) (doubledRight left right) ≫ join)
    rw [← Category.assoc j,
      show j ≫ blockCopair left (right ≫ coprod.inl) = right ≫ coprod.inl from inr_blockCopair _ _,
      ← Category.assoc j,
      show j ≫ blockCopair (doubledLeft left right) (doubledRight left right) =
        doubledRight left right from inr_blockCopair _ _, doubledRight, Category.assoc, Category.assoc]
    unfold dispatchRows
    rw [coprod.inl_desc_assoc]

theorem iterate_step (left : Obj X ⟶ Ports) (right : Obj Y ⟶ Exit ⨿ Obj X) :
    let cut := left ≫ coprod.desc (𝟙 (Exit ⨿ Obj X)) right
    iterate (step left right) = blockCopair (iterate cut) (right ≫ coprod.desc (𝟙 Exit) (iterate cut)) := by
  have e := iterate_join_blocks X Y Exit left (right ≫ coprod.inl)
  have terminal : iterate (right ≫ (coprod.inl : Exit ⨿ Obj X ⟶ Ports)) = right := by
    calc
      _ = (right ≫ coprod.inl) ≫ coprod.desc (𝟙 _) (iterate (right ≫ coprod.inl)) := iterate_fixpoint _
      _ = _ := by simp
  dsimp only at e ⊢
  rw [terminal] at e
  exact e

theorem iterate_double_iff (left : Obj X ⟶ Ports) (right : Obj Y ⟶ Exit ⨿ Obj X) :
    let cut := left ≫ coprod.desc (𝟙 (Exit ⨿ Obj X)) right
    let rightCut := iterate (doubledRight left right)
    let doubleCut := doubledLeft left right ≫ coprod.desc (𝟙 (Exit ⨿ Obj X)) rightCut
    iterate (step left right ≫ coprod.desc coprod.inl (step left right)) = iterate (step left right) ↔
      iterate doubleCut = iterate cut ∧
      rightCut ≫ coprod.desc (𝟙 Exit) (iterate cut) = right ≫ coprod.desc (𝟙 Exit) (iterate cut) := by
  dsimp only
  rw [doubled_eq, iterate_step, iterate_join_blocks]
  constructor
  · intro eq
    have hl := congrArg ((sumCofan X Y).inl ≫ ·) eq
    have hr := congrArg ((sumCofan X Y).inr ≫ ·) eq
    simp only [inl_blockCopair] at hl
    simp only [inr_blockCopair, hl] at hr
    exact ⟨hl, hr⟩
  · rintro ⟨hl, hr⟩
    rw [hl, hr]

theorem embedded_double_iff (row : Obj X ⟶ Exit ⨿ Obj X) (right : Obj Y ⟶ Exit ⨿ Obj X) :
    let g := step (row ≫ coprod.inl) right
    iterate (g ≫ coprod.desc coprod.inl g) = iterate g ↔
      iterate (row ≫ coprod.desc coprod.inl row) = iterate row := by
  dsimp only
  have residual := iterate_double_iff (Y := Y) (row ≫ coprod.inl) right
  dsimp only at residual
  rw [residual]
  let advance : Obj Y ⟶ Exit ⨿ Obj X := right ≫ coprod.desc coprod.inl row
  have cut : (row ≫ (coprod.inl : Exit ⨿ Obj X ⟶ Ports)) ≫
      coprod.desc (𝟙 (Exit ⨿ Obj X)) right = row := by simp
  have second : afterLeft (Y := Y) (row ≫ coprod.inl) =
      coprod.desc coprod.inl row ≫ coprod.inl := by
    simp only [afterLeft, coprod.desc_comp]
  have rightCut : iterate (doubledRight (row ≫ coprod.inl) right) = advance := by
    unfold doubledRight
    rw [second, ← Category.assoc]
    change iterate (advance ≫ coprod.inl) = advance
    calc
      _ = (advance ≫ coprod.inl) ≫ coprod.desc (𝟙 _) (iterate (advance ≫ coprod.inl)) := iterate_fixpoint _
      _ = _ := by simp
  have leftCut : doubledLeft (row ≫ coprod.inl) right ≫ coprod.desc
      (𝟙 (Exit ⨿ Obj X)) advance = row ≫ coprod.desc coprod.inl row := by
    simp only [doubledLeft, second, Category.assoc, coprod.inl_desc, Category.comp_id]
  rw [cut, rightCut, leftCut]
  constructor
  · exact And.left
  · intro eq
    refine ⟨eq, ?_⟩
    unfold advance
    rw [Category.assoc, coprod.desc_comp, coprod.inl_desc, ← iterate_fixpoint row]

theorem iterate_regrouping {Z : τ}
    (g : S ⟶ Exit ⨿ S) (h : Obj Z ⟶ Exit ⨿ Obj Z) (e : S ≅ Obj Z)
    (square : g ≫ coprod.map (𝟙 Exit) e.hom = e.hom ≫ h) :
    iterate g = e.hom ≫ iterate h := by
  let row := h ≫ coprod.map (𝟙 Exit) e.inv
  have descend : (coprod.map (𝟙 Exit) e.hom) ≫ coprod.map (𝟙 Exit) e.inv = 𝟙 _ := by
    apply coprod.hom_ext <;> simp
  have ascend : (coprod.map (𝟙 Exit) e.inv) ≫ coprod.map (𝟙 Exit) e.hom = 𝟙 _ := by
    apply coprod.hom_ext <;> simp
  have hg : g = e.hom ≫ row := by
    unfold row
    rw [← Category.assoc e.hom, ← square, Category.assoc, descend, Category.comp_id]
  have hh : row ≫ coprod.map (𝟙 Exit) e.hom = h := by
    unfold row
    rw [Category.assoc, ascend, Category.comp_id]
  rw [hg, iterate_roll, hh]

theorem iterate_double_of_regrouping {Z : τ}
    (g : S ⟶ Exit ⨿ S) (h : Obj Z ⟶ Exit ⨿ Obj Z) (e : S ≅ Obj Z)
    (square : g ≫ coprod.map (𝟙 Exit) e.hom = e.hom ≫ h)
    (doubles : iterate (h ≫ coprod.desc coprod.inl h) = iterate h) :
    iterate (g ≫ coprod.desc coprod.inl g) = iterate g := by
  have dispatch : coprod.desc coprod.inl (e.hom ≫ h) =
      coprod.map (𝟙 Exit) e.hom ≫ coprod.desc coprod.inl h := by
    apply coprod.hom_ext <;> simp
  have doubleSquare : (g ≫ coprod.desc coprod.inl g) ≫ coprod.map (𝟙 Exit) e.hom =
      e.hom ≫ (h ≫ coprod.desc coprod.inl h) := by
    rw [Category.assoc, coprod.desc_comp, coprod.inl_map, Category.id_comp, square,
      dispatch, ← Category.assoc g, square, Category.assoc]
  rw [iterate_regrouping _ _ e doubleSquare, doubles, iterate_regrouping _ _ e square]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OneSidedDoubling
