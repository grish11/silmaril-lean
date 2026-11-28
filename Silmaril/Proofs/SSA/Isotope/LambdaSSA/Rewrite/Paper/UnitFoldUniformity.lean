module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.StructuralValues.Freyd.Iteration.Elgot.Projection.HiddenBit.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Uniformity.Thms

/-! # Constructor discard proves binary-fold uniformity at syntax unit -/

public section

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.Extension.Singleton
open Paper.WithCaseReturns.StructuralValues.HiddenBit

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnitFoldUniformity

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "P" => Paper.TypeCategory (τ := τ) Φ
local notation "sunit" => (Silmaril.unit : τ)
local notation "U" => Paper.TypeCategory.ofType (Φ := Φ) sunit

section UnitPower

variable (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
  (includeUnit : ∀ {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ},
    Paper.WithUnitEta.Step Γ r s L → Seed Γ r s L)

local notation "Q" => TypeCategory Seed
local notation "F" => projection Seed
local notation "T" => Paper.TypeCategory.ofType (Φ := Φ) (Silmaril.coprod sunit sunit)
local notation "reset" => Paper.TypeCategory.discardArrow (Φ := Φ) sunit
local notation "drop" => Paper.TypeCategory.discardArrow (Φ := Φ) (Silmaril.coprod sunit sunit)

private abbrev tagL : U ⟶ T := (Paper.TypeCategory.sumCofan (Φ := Φ) sunit sunit).inl
private abbrev tagR : U ⟶ T := (Paper.TypeCategory.sumCofan (Φ := Φ) sunit sunit).inr

private theorem reset_idem : reset ≫ reset = reset :=
  Paper.TypeCategory.discard_comp_branchValue (Φ := Φ) (.unit (Γ := [sunit]))

private theorem tagL_drop : (tagL (τ := τ) (Φ := Φ)) ≫ drop = reset := by
  unfold tagL
  rw [Paper.TypeCategory.sumCofan_inl]
  exact Paper.TypeCategory.discard_comp_branchValue (.inl (.var rfl))

private theorem tagR_drop : (tagR (τ := τ) (Φ := Φ)) ≫ drop = reset := by
  unfold tagR
  rw [Paper.TypeCategory.sumCofan_inr]
  exact Paper.TypeCategory.discard_comp_branchValue (.inr (.var rfl))

local notation "c" => PreservesColimitPair.iso (F)

set_option backward.isDefEq.respectTransparency false in
private theorem mapSnd {X Y Z : P} (h : X ⟶ Y) :
    (c Z X).inv ≫ coprod.map (𝟙 ((F).obj Z)) ((F).map h) =
      (F).map (coprod.map (𝟙 Z) h) ≫ (c Z Y).inv := by
  rw [← (F).map_id Z]
  exact coprodComparison_inv_map Seed (𝟙 Z) h

private noncomputable abbrev unitSumIso : (F).obj U ⨿ (F).obj U ≅ (F).obj T :=
  (c U U) ≪≫ ((F).mapIso (Paper.TypeCategory.sumIso (Φ := Φ) sunit sunit)).symm

set_option backward.isDefEq.respectTransparency false in
private theorem unitSumIso_inl :
    coprod.inl ≫ (unitSumIso (τ := τ) (Φ := Φ) Seed).hom = (F).map tagL := by
  have tagCmp : tagL ≫ (Paper.TypeCategory.sumIso (Φ := Φ) sunit sunit).hom = coprod.inl :=
    Paper.TypeCategory.sumCofan_inl_sumIso_hom sunit sunit
  change coprod.inl ≫ (c U U).hom ≫ (F).map (Paper.TypeCategory.sumIso sunit sunit).inv = _
  rw [PreservesColimitPair.iso_hom, inl_coprodComparison_assoc, ← Functor.map_comp,
    ← tagCmp, Category.assoc, Iso.hom_inv_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private theorem unitSumIso_inr :
    coprod.inr ≫ (unitSumIso (τ := τ) (Φ := Φ) Seed).hom = (F).map tagR := by
  have tagCmp : tagR ≫ (Paper.TypeCategory.sumIso (Φ := Φ) sunit sunit).hom = coprod.inr :=
    Paper.TypeCategory.sumCofan_inr_sumIso_hom sunit sunit
  change coprod.inr ≫ (c U U).hom ≫ (F).map (Paper.TypeCategory.sumIso sunit sunit).inv = _
  rw [PreservesColimitPair.iso_hom, inr_coprodComparison_assoc, ← Functor.map_comp,
    ← tagCmp, Category.assoc, Iso.hom_inv_id, Category.comp_id]

local notation "QU" => ofType Seed sunit

set_option backward.isDefEq.respectTransparency false in
include includeUnit in
private theorem transported_drop :
    (unitSumIso Seed).hom ≫ (F).map drop = coprod.desc (𝟙 ((F).obj U)) (𝟙 ((F).obj U)) := by
  have eta : (F).map reset = 𝟙 _ := unit_eta_of_include Seed includeUnit
  apply coprod.hom_ext
  · rw [← Category.assoc, unitSumIso_inl, ← Functor.map_comp, tagL_drop, eta, coprod.inl_desc]
  · rw [← Category.assoc, unitSumIso_inr, ← Functor.map_comp, tagR_drop, eta, coprod.inr_desc]

private theorem unitSumIso_hom_eq :
    (unitSumIso Seed).hom = (sumIso Seed sunit sunit).inv := by
  have h := congrArg Iso.inv (projection_mapIso_sumIso Seed sunit sunit)
  change (F).map (Paper.TypeCategory.sumIso sunit sunit).inv =
    (c U U).inv ≫ (sumIso Seed sunit sunit).inv at h
  change (c U U).hom ≫ (F).map (Paper.TypeCategory.sumIso sunit sunit).inv = _
  rw [h, Iso.hom_inv_id_assoc]

private theorem unitSumIso_inv_eq :
    (unitSumIso Seed).inv = (sumIso Seed sunit sunit).hom := by
  apply (cancel_epi (unitSumIso Seed).hom).1
  rw [Iso.hom_inv_id, unitSumIso_hom_eq, Iso.inv_hom_id]

set_option backward.isDefEq.respectTransparency false in
include includeUnit in
theorem project_unit_row_comp_fold {B : P} (row : U ⟶ B ⨿ T) :
    ((F).map row ≫ (c B T).inv ≫ coprod.map (𝟙 ((F).obj B)) (sumIso Seed sunit sunit).hom) ≫
      coprod.map (𝟙 ((F).obj B)) (coprod.desc (𝟙 QU) (𝟙 QU)) =
        projectStep Seed (row ≫ coprod.map (𝟙 B) drop) := by
  have foldEq : (sumIso Seed sunit sunit).hom ≫ coprod.desc (𝟙 QU) (𝟙 QU) = (F).map drop := by
    apply (cancel_epi (sumIso Seed sunit sunit).inv).1
    rw [Iso.inv_hom_id_assoc, ← unitSumIso_hom_eq, transported_drop Seed includeUnit]
  change _ = (F).map (row ≫ coprod.map (𝟙 B) drop) ≫ (c B U).inv
  rw [Category.assoc, Category.assoc, coprod.map_map, Category.id_comp, foldEq,
    mapSnd, ← Functor.map_comp_assoc]

set_option backward.isDefEq.respectTransparency false in
include includeUnit in
theorem unit_fold_of_native_rows {B : P}
    (left right : U ⟶ B ⨿ T) (g : U ⟶ B ⨿ U)
    (leftErase : left ≫ coprod.map (𝟙 B) drop = g)
    (rightErase : right ≫ coprod.map (𝟙 B) drop = g) :
    let projectRow := fun a : U ⟶ B ⨿ T =>
      (F).map a ≫ (c B T).inv ≫ coprod.map (𝟙 ((F).obj B)) (sumIso Seed sunit sunit).hom
    iterateChosen Seed (coprod.desc (projectRow left) (projectRow right)) =
      coprod.desc (𝟙 QU) (𝟙 QU) ≫ iterateChosen Seed (projectStep Seed g) := by
  let b : T ⟶ B ⨿ T := (Paper.TypeCategory.sumIso sunit sunit).hom ≫
    coprod.desc (reset ≫ left) (reset ≫ right)
  let k : QU ⨿ QU ⟶ QU := coprod.desc (𝟙 QU) (𝟙 QU)
  let i := unitSumIso Seed
  have leftEq : tagL ≫ b = reset ≫ left := by
    change (Paper.TypeCategory.sumCofan sunit sunit).inl ≫
      (Paper.TypeCategory.sumIso sunit sunit).hom ≫ _ = _
    rw [← Category.assoc, Paper.TypeCategory.sumCofan_inl_sumIso_hom, coprod.inl_desc]
  have rightEq : tagR ≫ b = reset ≫ right := by
    change (Paper.TypeCategory.sumCofan sunit sunit).inr ≫
      (Paper.TypeCategory.sumIso sunit sunit).hom ≫ _ = _
    rw [← Category.assoc, Paper.TypeCategory.sumCofan_inr_sumIso_hom, coprod.inr_desc]
  have native : b ≫ coprod.map (𝟙 B) drop = drop ≫ (reset ≫ g) := by
    apply BinaryCofan.IsColimit.hom_ext (Paper.TypeCategory.sumCofanIsColimit sunit sunit)
    · change tagL ≫ (b ≫ _) = tagL ≫ (drop ≫ reset ≫ g)
      rw [← Category.assoc, leftEq, Category.assoc, leftErase, ← Category.assoc tagL drop,
        tagL_drop, ← Category.assoc reset reset, reset_idem]
    · change tagR ≫ (b ≫ _) = tagR ≫ (drop ≫ reset ≫ g)
      rw [← Category.assoc, rightEq, Category.assoc, rightErase, ← Category.assoc tagR drop,
        tagR_drop, ← Category.assoc reset reset, reset_idem]
  let row := fun a : U ⟶ B ⨿ T =>
    (F).map a ≫ (c B T).inv ≫ coprod.map (𝟙 ((F).obj B)) i.inv
  let f := coprod.desc (row left) (row right)
  have eta : (F).map reset = 𝟙 QU := unit_eta_of_include Seed includeUnit
  have coord : f ≫ coprod.map (𝟙 ((F).obj B)) i.hom = i.hom ≫ projectStep Seed b := by
    dsimp only [f]
    apply coprod.hom_ext
    · rw [coprod.inl_desc_assoc, ← Category.assoc coprod.inl i.hom,
        show coprod.inl ≫ i.hom = (F).map tagL from unitSumIso_inl Seed]
      change row left ≫ coprod.map (𝟙 ((F).obj B)) i.hom =
        (F).map tagL ≫ (F).map b ≫ (c B T).inv
      rw [← Functor.map_comp_assoc, leftEq, Functor.map_comp, eta, Category.id_comp]
      simp only [row, Category.assoc, coprod.map_map, Iso.inv_hom_id, coprod.map_id_id, Category.comp_id]
    · rw [coprod.inr_desc_assoc, ← Category.assoc coprod.inr i.hom,
        show coprod.inr ≫ i.hom = (F).map tagR from unitSumIso_inr Seed]
      change row right ≫ coprod.map (𝟙 ((F).obj B)) i.hom =
        (F).map tagR ≫ (F).map b ≫ (c B T).inv
      rw [← Functor.map_comp_assoc, rightEq, Functor.map_comp, eta, Category.id_comp]
      simp only [row, Category.assoc, coprod.map_map, Iso.inv_hom_id, coprod.map_id_id, Category.comp_id]
  have out : projectStep Seed (reset ≫ g) = projectStep Seed g := by
    change (F).map (reset ≫ g) ≫ (c B U).inv = _
    rw [Functor.map_comp, eta, Category.id_comp]
  have replay := uniformity_of_constructor_square Seed
    (show Paper.TypeCategory.ConstructorReturn (drop : T ⟶ U) from ⟨.unit, .unit, rfl⟩)
    b (reset ≫ g) native
  have answer : iterateChosen Seed f = k ≫ iterateChosen Seed (projectStep Seed g) := by
    rw [uniformity_of_iso Seed i _ _ coord, replay, ← Category.assoc,
      show i.hom ≫ (F).map drop = k from transported_drop Seed includeUnit, out]
  simpa only [f, row, i, unitSumIso_inv_eq] using answer

private noncomputable def swapUnitTags : T ⟶ T :=
  (Paper.TypeCategory.sumIso sunit sunit).hom ≫ coprod.desc tagR tagL

private theorem tagL_swap : (tagL (τ := τ) (Φ := Φ)) ≫ swapUnitTags = tagR := by
  rw [swapUnitTags, ← Category.assoc, show tagL ≫ (Paper.TypeCategory.sumIso sunit sunit).hom = coprod.inl from
    Paper.TypeCategory.sumCofan_inl_sumIso_hom sunit sunit, coprod.inl_desc]

private theorem tagR_swap : (tagR (τ := τ) (Φ := Φ)) ≫ swapUnitTags = tagL := by
  rw [swapUnitTags, ← Category.assoc, show tagR ≫ (Paper.TypeCategory.sumIso sunit sunit).hom = coprod.inr from
    Paper.TypeCategory.sumCofan_inr_sumIso_hom sunit sunit, coprod.inr_desc]

private theorem swap_drop : swapUnitTags ≫ drop = drop := by
  apply BinaryCofan.IsColimit.hom_ext (Paper.TypeCategory.sumCofanIsColimit sunit sunit)
  · change tagL ≫ (swapUnitTags ≫ drop) = tagL ≫ drop
    rw [← Category.assoc, tagL_swap, tagR_drop, tagL_drop]
  · change tagR ≫ (swapUnitTags ≫ drop) = tagR ≫ drop
    rw [← Category.assoc, tagR_swap, tagL_drop, tagR_drop]

set_option backward.isDefEq.respectTransparency false in
private theorem transported_swap :
    (unitSumIso Seed).hom ≫ (F).map swapUnitTags =
      coprod.desc coprod.inr coprod.inl ≫ (unitSumIso Seed).hom := by
  apply coprod.hom_ext
  · rw [← Category.assoc, ← Category.assoc, unitSumIso_inl, coprod.inl_desc,
      unitSumIso_inr, ← Functor.map_comp, tagL_swap]
  · rw [← Category.assoc, ← Category.assoc, unitSumIso_inr, coprod.inr_desc,
      unitSumIso_inl, ← Functor.map_comp, tagR_swap]

set_option backward.isDefEq.respectTransparency false in
include includeUnit in
theorem unit_fold_of_shared_choice {B : Q} (g : QU ⟶ B ⨿ (QU ⨿ QU)) :
    iterateChosen Seed (coprod.desc g (g ≫ coprod.map (𝟙 B) (coprod.desc coprod.inr coprod.inl))) =
      coprod.desc (𝟙 QU) (𝟙 QU) ≫
        iterateChosen Seed (g ≫ coprod.map (𝟙 B) (coprod.desc (𝟙 QU) (𝟙 QU))) := by
  let i := unitSumIso Seed
  let k : QU ⨿ QU ⟶ QU := coprod.desc (𝟙 QU) (𝟙 QU)
  let swap : QU ⨿ QU ⟶ QU ⨿ QU := coprod.desc coprod.inr coprod.inl
  obtain ⟨a, ha⟩ := (F).map_surjective (X := U) (Y := B.as ⨿ T)
    (g ≫ coprod.map (𝟙 B) i.hom ≫ (c B.as T).hom)
  have base : (F).map a ≫ (c B.as T).inv = g ≫ coprod.map (𝟙 B) i.hom := by
    rw [ha]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let row := fun a : U ⟶ B.as ⨿ T =>
    (F).map a ≫ (c B.as T).inv ≫ coprod.map (𝟙 B) i.inv
  have left : row a = g := by
    dsimp only [row]
    rw [← Category.assoc, base]
    simp only [Category.assoc, coprod.map_map, Iso.hom_inv_id, coprod.map_id_id, Category.comp_id]
  have right : row (a ≫ coprod.map (𝟙 B.as) swapUnitTags) = g ≫ coprod.map (𝟙 B) swap := by
    dsimp only [row]
    have compare := mapSnd Seed (Z := B.as) swapUnitTags
    rw [Functor.map_comp, Category.assoc, ← reassoc_of% compare, ← Category.assoc ((F).map a), base]
    simp only [Category.assoc, coprod.map_map, Category.id_comp]
    rw [reassoc_of% transported_swap Seed, Iso.hom_inv_id, Category.comp_id]
  have target : projectStep Seed (a ≫ coprod.map (𝟙 B.as) drop) = g ≫ coprod.map (𝟙 B) k := by
    change (F).map (a ≫ coprod.map (𝟙 B.as) drop) ≫ (c B.as U).inv = _
    rw [Functor.map_comp, Category.assoc, ← mapSnd, ← Category.assoc, base, Category.assoc,
      coprod.map_map, Category.id_comp, transported_drop Seed includeUnit]
    rfl
  have erase :
      (a ≫ coprod.map (𝟙 B.as) swapUnitTags) ≫ coprod.map (𝟙 B.as) drop =
        a ≫ coprod.map (𝟙 B.as) drop := by
    rw [Category.assoc, coprod.map_map, Category.id_comp, swap_drop]
  have replay := unit_fold_of_native_rows Seed includeUnit a
    (a ≫ coprod.map (𝟙 B.as) swapUnitTags) (a ≫ coprod.map (𝟙 B.as) drop) rfl erase
  rw [← unitSumIso_inv_eq Seed] at replay
  change iterateChosen Seed (coprod.desc (row a) (row (a ≫ coprod.map (𝟙 B.as) swapUnitTags))) =
    k ≫ iterateChosen Seed (projectStep Seed (a ≫ coprod.map (𝟙 B.as) drop)) at replay
  simpa only [left, right, target] using replay

set_option backward.isDefEq.respectTransparency false in
include includeUnit in
theorem unit_alternate_power_of_seed {B : Q} (g : (F).obj U ⟶ B ⨿ (F).obj U) :
    iterateChosen Seed (g ≫ coprod.desc coprod.inl g) = iterateChosen Seed g := by
  let k : QU ⨿ QU ⟶ QU := coprod.desc (𝟙 QU) (𝟙 QU)
  let right : QU ⟶ QU ⨿ QU := coprod.inr
  let swap : QU ⨿ QU ⟶ QU ⨿ QU := coprod.desc coprod.inr coprod.inl
  have switch : right ≫ swap = coprod.inl := coprod.inr_desc _ _
  have erase : right ≫ k = 𝟙 QU := coprod.inr_desc _ _
  have eq := unit_fold_of_shared_choice Seed includeUnit (g ≫ coprod.map (𝟙 B) right)
  change iterateChosen Seed (coprod.desc (g ≫ coprod.map (𝟙 B) right)
    ((g ≫ coprod.map (𝟙 B) right) ≫ coprod.map (𝟙 B) swap)) =
      k ≫ iterateChosen Seed ((g ≫ coprod.map (𝟙 B) right) ≫ coprod.map (𝟙 B) k) at eq
  simp only [Category.assoc, coprod.map_map, switch, erase,
    coprod.map_id_id, Category.comp_id] at eq
  exact (alternating_fold_iff_double_of_seed Seed g).1 eq

end UnitPower

variable {ε : Type w} [HasEff Φ ε] (pe : ε)

local notation "Seed" => Paper.WithCaseReturns.JoinedStep (τ := τ) (Φ := Φ) pe
local notation "Q" => TypeCategory Seed

theorem unit_alternate_power {B : Q} (g : ofType Seed sunit ⟶ B ⨿ ofType Seed sunit) :
    iterateChosen Seed (g ≫ coprod.desc coprod.inl g) = iterateChosen Seed g :=
  unit_alternate_power_of_seed Seed (Paper.WithCaseReturns.includeUnit pe) g

local notation "Obj" => ofType Seed
local notation "I" => iterateChosen Seed

private theorem unit_fold_of_right_switch {B : Q}
    (f : Obj sunit ⨿ Obj sunit ⟶ B ⨿ (Obj sunit ⨿ Obj sunit))
    (g : Obj sunit ⟶ B ⨿ Obj sunit)
    (square : f ≫ coprod.map (𝟙 B) (coprod.desc (𝟙 (Obj sunit)) (𝟙 (Obj sunit))) =
      coprod.desc (𝟙 (Obj sunit)) (𝟙 (Obj sunit)) ≫ g)
    (switch : coprod.inr ≫ f = g ≫ coprod.map (𝟙 B) (coprod.inl : Obj sunit ⟶ _)) :
    I f = coprod.desc (𝟙 (Obj sunit)) (𝟙 (Obj sunit)) ≫ I g :=
  binary_fold_of_right_switch_and_double pe f g square switch (unit_alternate_power pe _)

local notation "Bit" => Silmaril.coprod sunit sunit
local notation "State" => Obj (Silmaril.product sunit Bit)
local notation "p" => productFst Seed sunit Bit

theorem unit_reset_of_right_switch {B : Q} (f : State ⟶ B ⨿ State) (g : Obj sunit ⟶ B ⨿ Obj sunit)
    (square : f ≫ coprod.map (𝟙 B) p = p ≫ g)
    (switch : rightMode pe sunit ≫ f = g ≫ coprod.map (𝟙 B) (leftMode pe sunit)) :
    I f = I (f ≫ coprod.map (𝟙 B) (p ≫ leftMode pe sunit)) := by
  let e := modes (τ := τ) (Φ := Φ) pe sunit
  let d := e.hom ≫ f ≫ coprod.map (𝟙 B) e.inv
  let k : Obj sunit ⨿ Obj sunit ⟶ Obj sunit := coprod.desc (𝟙 _) (𝟙 _)
  have fold : e.hom ≫ p = k := modes_fst pe sunit
  have recover : e.inv ≫ k = p := by rw [← fold, Iso.inv_hom_id_assoc]
  have foldedSquare : d ≫ coprod.map (𝟙 B) k = k ≫ g := by
    dsimp only [d]
    rw [Category.assoc, Category.assoc, coprod.map_map, Category.id_comp,
      recover, square, ← Category.assoc, fold]
  have switched : coprod.inr ≫ d = g ≫ coprod.map (𝟙 B) (coprod.inl : Obj sunit ⟶ _) := by
    dsimp only [d]
    rw [← Category.assoc, show coprod.inr ≫ e.hom = rightMode pe sunit from rfl,
      ← Category.assoc, switch, Category.assoc, coprod.map_map, Category.id_comp]
    have back : leftMode pe sunit ≫ e.inv = coprod.inl := by
      change (coprod.inl ≫ e.hom) ≫ e.inv = _
      rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [back]
  have compare : d ≫ coprod.map (𝟙 B) e.hom = e.hom ≫ f := by
    simp only [d, Category.assoc, coprod.map_map, Iso.inv_hom_id, coprod.map_id_id, Category.comp_id]
  have eq := (uniformity_of_iso Seed e d f compare).symm.trans
    (unit_fold_of_right_switch pe d g foldedSquare switched)
  change e.hom ≫ I f = k ≫ I g at eq
  rw [← fold, Category.assoc] at eq
  have uniform : I f = p ≫ I g := (cancel_epi e.hom).1 eq
  exact (uniformity_iff_reset Seed p (leftMode pe sunit) (leftMode_fst pe sunit) f g square).1 uniform

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnitFoldUniformity
