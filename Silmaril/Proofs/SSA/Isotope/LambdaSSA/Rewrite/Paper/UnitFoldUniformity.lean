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

private noncomputable abbrev boundedUnitStep {B : P} (b : U ⟶ B ⨿ U) : U ⟶ B ⨿ U :=
  reset ≫ b ≫ coprod.map (𝟙 B) reset

private noncomputable abbrev alternatingUnitStep {B : P} (b : U ⟶ B ⨿ U) : T ⟶ B ⨿ T :=
  (Paper.TypeCategory.sumIso (Φ := Φ) sunit sunit).hom ≫
    coprod.desc (boundedUnitStep b ≫ coprod.map (𝟙 B) tagR)
      (boundedUnitStep b ≫ coprod.map (𝟙 B) tagL)

private theorem tagL_alternate {B : P} (b : U ⟶ B ⨿ U) :
    tagL ≫ alternatingUnitStep b = boundedUnitStep b ≫ coprod.map (𝟙 B) tagR := by
  unfold alternatingUnitStep
  rw [← Category.assoc tagL, show tagL ≫ (Paper.TypeCategory.sumIso sunit sunit).hom = coprod.inl from
    Paper.TypeCategory.sumCofan_inl_sumIso_hom sunit sunit, coprod.inl_desc]

private theorem tagR_alternate {B : P} (b : U ⟶ B ⨿ U) :
    tagR ≫ alternatingUnitStep b = boundedUnitStep b ≫ coprod.map (𝟙 B) tagL := by
  unfold alternatingUnitStep
  rw [← Category.assoc tagR, show tagR ≫ (Paper.TypeCategory.sumIso sunit sunit).hom = coprod.inr from
    Paper.TypeCategory.sumCofan_inr_sumIso_hom sunit sunit, coprod.inr_desc]

/-- A square in standard Paper. Reset the unit payload on both the input and feedback sides. -/
private theorem paper_discard_square {B : P} (b : U ⟶ B ⨿ U) :
    alternatingUnitStep b ≫ coprod.map (𝟙 B) drop = drop ≫ boundedUnitStep b := by
  apply BinaryCofan.IsColimit.hom_ext (Paper.TypeCategory.sumCofanIsColimit sunit sunit)
  · change tagL ≫ (alternatingUnitStep b ≫ _) = tagL ≫ (drop ≫ boundedUnitStep b)
    rw [← Category.assoc tagL (alternatingUnitStep b), tagL_alternate,
      ← Category.assoc tagL drop, tagL_drop, Category.assoc, coprod.map_map, Category.id_comp, tagR_drop]
    simp only [boundedUnitStep, Category.assoc, coprod.map_map, Category.id_comp, reset_idem]
    rw [← Category.assoc reset reset, reset_idem]
  · change tagR ≫ (alternatingUnitStep b ≫ _) = tagR ≫ (drop ≫ boundedUnitStep b)
    rw [← Category.assoc tagR (alternatingUnitStep b), tagR_alternate,
      ← Category.assoc tagR drop, tagR_drop, Category.assoc, coprod.map_map, Category.id_comp, tagL_drop]
    simp only [boundedUnitStep, Category.assoc, coprod.map_map, Category.id_comp, reset_idem]
    rw [← Category.assoc reset reset, reset_idem]

local notation "c" => PreservesColimitPair.iso (F)

set_option backward.isDefEq.respectTransparency false in
private theorem mapSnd {X Y Z : P} (h : X ⟶ Y) :
    (c Z X).inv ≫ coprod.map (𝟙 ((F).obj Z)) ((F).map h) =
      (F).map (coprod.map (𝟙 Z) h) ≫ (c Z Y).inv := by
  rw [← (F).map_id Z]
  exact coprodComparison_inv_map Seed (𝟙 Z) h

include includeUnit in
private theorem projectedUnitStep {B : P} (b : U ⟶ B ⨿ U) :
    projectStep Seed (boundedUnitStep b) = projectStep Seed b := by
  have unitEta : (F).map reset = 𝟙 _ :=
    unit_eta_of_include Seed includeUnit
  have comm : (F).map (b ≫ coprod.map (𝟙 B) reset) = (F).map (reset ≫ boundedUnitStep b) := by
    change (F).map (b ≫ coprod.map (𝟙 B) reset) =
      (F).map (reset ≫ reset ≫ b ≫ coprod.map (𝟙 B) reset)
    rw [Functor.map_comp (F) reset, unitEta, Category.id_comp,
      Functor.map_comp (F) reset, unitEta, Category.id_comp]
  have e := (projectSquare_iff Seed b (boundedUnitStep b) reset).2 comm
  simpa only [unitEta, coprod.map_id_id, Category.comp_id, Category.id_comp] using e.symm

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

private noncomputable abbrev alternate {B : Q} (g : QU ⟶ B ⨿ QU) :
    QU ⨿ QU ⟶ B ⨿ (QU ⨿ QU) :=
  coprod.desc (g ≫ coprod.map (𝟙 B) coprod.inr) (g ≫ coprod.map (𝟙 B) coprod.inl)

set_option backward.isDefEq.respectTransparency false in
private theorem transported_alternate {B : P} (b : U ⟶ B ⨿ U) :
    (unitSumIso Seed).hom ≫ projectStep Seed (alternatingUnitStep b) =
      alternate Seed (projectStep Seed (boundedUnitStep b)) ≫
        coprod.map (𝟙 ((F).obj B)) (unitSumIso Seed).hom := by
  apply coprod.hom_ext
  · rw [← Category.assoc, unitSumIso_inl, alternate, coprod.inl_desc_assoc, Category.assoc,
      coprod.map_map, Category.id_comp, unitSumIso_inr]
    change (F).map tagL ≫ (F).map (alternatingUnitStep b) ≫ (c B T).inv =
      ((F).map (boundedUnitStep b) ≫ (c B U).inv) ≫ _
    rw [← Functor.map_comp_assoc, tagL_alternate, Functor.map_comp, Category.assoc,
      Category.assoc, mapSnd]
  · rw [← Category.assoc, unitSumIso_inr, alternate, coprod.inr_desc_assoc, Category.assoc,
      coprod.map_map, Category.id_comp, unitSumIso_inl]
    change (F).map tagR ≫ (F).map (alternatingUnitStep b) ≫ (c B T).inv =
      ((F).map (boundedUnitStep b) ≫ (c B U).inv) ≫ _
    rw [← Functor.map_comp_assoc, tagR_alternate, Functor.map_comp, Category.assoc,
      Category.assoc, mapSnd]

set_option backward.isDefEq.respectTransparency false in
include includeUnit in
private theorem transported_drop :
    (unitSumIso Seed).hom ≫ (F).map drop = coprod.desc (𝟙 ((F).obj U)) (𝟙 ((F).obj U)) := by
  have eta : (F).map reset = 𝟙 _ := unit_eta_of_include Seed includeUnit
  apply coprod.hom_ext
  · rw [← Category.assoc, unitSumIso_inl, ← Functor.map_comp, tagL_drop, eta, coprod.inl_desc]
  · rw [← Category.assoc, unitSumIso_inr, ← Functor.map_comp, tagR_drop, eta, coprod.inr_desc]

set_option backward.isDefEq.respectTransparency false in
include includeUnit in
theorem unit_alternate_power_of_seed {B : Q} (g : (F).obj U ⟶ B ⨿ (F).obj U) :
    iterateChosen Seed (g ≫ coprod.desc coprod.inl g) = iterateChosen Seed g := by
  obtain ⟨b, hb⟩ := (F).map_surjective (X := U) (Y := B.as ⨿ U) (g ≫ (c B.as U).hom)
  have bEq : projectStep Seed b = g := by
    change (F).map b ≫ (c B.as U).inv = g
    rw [hb, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have gEq := (projectedUnitStep Seed includeUnit b).trans bEq
  have eq := uniformity_of_constructor_square Seed
    (show Paper.TypeCategory.ConstructorReturn (drop : T ⟶ U) from ⟨.unit, .unit, rfl⟩)
    (alternatingUnitStep b) (boundedUnitStep b) (paper_discard_square b)
  have transIso := uniformity_of_iso Seed (unitSumIso Seed) _ _ (transported_alternate Seed b).symm
  rw [eq, ← Category.assoc, transported_drop Seed includeUnit, gEq] at transIso
  exact (alternating_fold_iff_double_of_seed Seed g).1 transIso

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
