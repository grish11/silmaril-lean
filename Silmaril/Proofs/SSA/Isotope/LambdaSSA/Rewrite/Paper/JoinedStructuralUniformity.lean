module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.StructuralValues.Uniformity.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Acyclic.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Generation.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Obstruction.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.PairReturns

/-! # A stratified square and the two native replay boundaries -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedStructuralUniformity

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.WithPairReturns.StructuralValues.Uniformity
open scoped Paper.BoundSimulation.Obstruction Paper.WithPairReturns.StructuralValues.Uniformity
open Paper.Extension.Singleton
open Paper.Extension.Singleton.Generation (exactCopair_ofRegion)
open Paper.Extension.Singleton.ValueCoproducts (exactCopair)
open CfgEta.TypeCategory (caseValueBranches)

local notation "Obj" => ofType Seed
local notation "TyUnit" => Paper.WithPairReturns.StructuralValues.Uniformity.UnitTy
local notation "U" => Obj TyUnit
local notation "D" => Obj Bit
local notation "A" => Obj Three
local notation "split" => sumIso Seed TyUnit Bit
private abbrev left : U ⟶ A := (sumCofan Seed TyUnit Bit).inl
private abbrev right : D ⟶ A := (sumCofan Seed TyUnit Bit).inr
local notation "Lit" => ofRegion Seed

private theorem state_left : left ≫ stateMap = tag :=
  (sumCofanIsColimit Seed TyUnit Bit).fac (BinaryCofan.mk tag (𝟙 D)) ⟨WalkingPair.left⟩

private theorem state_right : right ≫ stateMap = 𝟙 D :=
  (sumCofanIsColimit Seed TyUnit Bit).fac (BinaryCofan.mk tag (𝟙 D)) ⟨WalkingPair.right⟩

private theorem left_split : left ≫ (split).hom = (coprod.inl : U ⟶ U ⨿ D) :=
  sumCofan_inl_sumIso_hom Seed TyUnit Bit

private theorem right_split : right ≫ (split).hom = (coprod.inr : D ⟶ U ⨿ D) :=
  sumCofan_inr_sumIso_hom Seed TyUnit Bit

private theorem tag_split : tag ≫ upperRow = (coprod.inl : U ⟶ U ⨿ U) :=
  sumCofan_inl_sumIso_hom Seed TyUnit TyUnit

private abbrev tagRight : U ⟶ D := (sumCofan Seed TyUnit TyUnit).inr

private theorem tagRight_split : tagRight ≫ upperRow = (coprod.inr : U ⟶ U ⨿ U) :=
  sumCofan_inr_sumIso_hom Seed TyUnit TyUnit

private theorem left_inv : (coprod.inl : U ⟶ U ⨿ D) ≫ (split).inv = left := by
  rw [← left_split, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem state_structural : StructuralValues.HomProperty Seed stateMap :=
  StructuralValues.copair_mem Seed (StructuralValues.sum_inl_mem Seed TyUnit TyUnit)
    ((StructuralValues.HomProperty Seed).id_mem D)

theorem joined_square :
    sourceStep ≫ coprod.map (𝟙 U) stateMap = stateMap ≫ targetStep := by
  apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit Seed TyUnit Bit)
  · change left ≫ (sourceStep ≫ _) = left ≫ (stateMap ≫ targetStep)
    simp only [sourceStep, targetStep, Category.assoc, reassoc_of% left_split,
      coprod.inl_desc_assoc, coprod.inl_map_assoc, coprod.inl_map, Category.id_comp,
      reassoc_of% state_left, reassoc_of% tag_split]
  · change right ≫ (sourceStep ≫ _) = right ≫ (stateMap ≫ targetStep)
    simp only [sourceStep, targetStep, Category.assoc, reassoc_of% right_split, coprod.inr_desc_assoc,
      coprod.map_map, Category.id_comp, left_inv, state_left, reassoc_of% state_right]

theorem source_bounded : AcyclicStep Seed U sourceStep := by
  have h := AcyclicStep.extend split upperRow (AcyclicStep.exits (Seed := Seed) (𝟙 U))
  simpa only [sourceStep, Category.id_comp] using h

theorem joined_iteration :
    iterateChosen Seed sourceStep = stateMap ≫ iterateChosen Seed targetStep :=
  uniformity_of_acyclic Seed stateMap source_bounded targetStep joined_square

theorem upper_right_transfer :
    (sumCofan Seed TyUnit TyUnit).inr ≫ (sumCofan Seed TyUnit Bit).inr ≫ sourceStep =
      (sumCofan Seed TyUnit Bit).inl ≫ (coprod.inr : A ⟶ U ⨿ A) := by
  change tagRight ≫ (right ≫ sourceStep) = left ≫ coprod.inr
  have step : right ≫ sourceStep = upperRow ≫ coprod.map (𝟙 U) left := by
    simp only [sourceStep, reassoc_of% right_split, coprod.inr_desc_assoc, left_inv]
  rw [step, reassoc_of% tagRight_split, coprod.inr_map]

open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer
  (Env EnvTy Result)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Observer
  (TermObservation evalRegionWith evalTermWith pair_join_same)
open scoped Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer.CanonicalUnit

private theorem tag_typed :
    ValueBranches [TyUnit] (.br 0 (.inl (.var 0)) : Region Empty) [Bit] :=
  .br rfl (.inl (.var rfl))

private theorem tag_repr : Lit tag_typed = tag :=
  (congrArg (projection Seed).map (Paper.TypeCategory.sumCofan_inl (Φ := Empty) TyUnit TyUnit)).symm

private theorem tagRight_typed :
    ValueBranches [TyUnit] (.br 0 (.inr (.var 0)) : Region Empty) [Bit] :=
  .br rfl (.inr (.var rfl))

private theorem tagRight_repr : Lit tagRight_typed = tagRight :=
  (congrArg (projection Seed).map (Paper.TypeCategory.sumCofan_inr (Φ := Empty) TyUnit TyUnit)).symm

private theorem id_typed : ValueBranches [Bit] (.br 0 (.var 0) : Region Empty) [Bit] :=
  .br rfl (.var rfl)

private theorem state_repr : stateMap = Lit (caseValueBranches tag_typed id_typed) := by
  have idEq : Lit id_typed = 𝟙 D := by
    change (projection Seed).map (Paper.TypeCategory.ofRegion id_typed) = _
    rw [Paper.TypeCategory.ofRegion_id]
    exact (projection Seed).map_id _
  rw [stateMap, ← tag_repr, ← idEq, exactCopair_ofRegion]

private def envLeft : Env := fun _ => .inl .unit
private def envRight : Env := fun _ => .inr (.inr .unit)

private theorem typedLeft : EnvTy [Three] envLeft := by
  intro i T h
  cases i with
  | zero => cases Option.some.inj h; exact .inl .unit
  | succ i => simp [At] at h

private theorem typedRight : EnvTy [Three] envRight := by
  intro i T h
  cases i with
  | zero => cases Option.some.inj h; exact .inr (.inr .unit)
  | succ i => simp [At] at h

private abbrev plain : TermObservation (α := Empty) Empty := {}

private theorem tags_ne : tag ≠ tagRight := by
  intro eq
  rw [← tag_repr, ← tagRight_repr] at eq
  have henv : EnvTy [TyUnit] (fun _ => .unit) := by
    intro i T h
    cases i with
    | zero => cases Option.some.inj h; exact .unit
    | succ i => simp [At] at h
  have obs := pair_join_same (observation := plain) rfl rfl ((ofRegion_eq_iff Seed _ _).1 eq) _ henv
  change Result.jump 0 (.inl .unit) = .jump 0 (.inr .unit) at obs
  cases obs

theorem state_not_mono : ¬ Mono stateMap := by
  intro mono
  have h : left ≫ stateMap = (tag ≫ right) ≫ stateMap := by
    rw [Category.assoc, state_left, state_right, Category.comp_id]
  have eq := (cancel_mono stateMap).mp h
  let alwaysRight := exactCopair Seed tagRight tagRight
  let discriminate := exactCopair Seed tag alwaysRight
  have dl : left ≫ discriminate = tag :=
    (sumCofanIsColimit Seed TyUnit Bit).fac (BinaryCofan.mk tag alwaysRight) ⟨WalkingPair.left⟩
  have dr : right ≫ discriminate = alwaysRight :=
    (sumCofanIsColimit Seed TyUnit Bit).fac (BinaryCofan.mk tag alwaysRight) ⟨WalkingPair.right⟩
  have constant : tag ≫ alwaysRight = tagRight :=
    (sumCofanIsColimit Seed TyUnit TyUnit).fac (BinaryCofan.mk tagRight tagRight) ⟨WalkingPair.left⟩
  have e := congrArg (· ≫ discriminate) eq
  rw [dl, Category.assoc, dr, constant] at e
  exact tags_ne e

private theorem inl_ne_right (t : Tm Empty) (env : Env) :
    evalRegionWith plain (.br 0 (.inl t)) env ≠ .jump 0 (.inr .unit) := by
  simp only [evalRegionWith, evalTermWith]
  cases evalTermWith plain t env <;> simp

private theorem inr_ne_left (t : Tm Empty) (env : Env) :
    evalRegionWith plain (.br 0 (.inr t)) env ≠ .jump 0 (.inl .unit) := by
  simp only [evalRegionWith, evalTermWith]
  cases evalTermWith plain t env <;> simp

set_option backward.isDefEq.respectTransparency false in
theorem no_constructor_state :
    ¬ ∃ (a : Tm Empty) (ha : Tm.BranchValue [Three] a Bit), stateMap = Lit (.br (ℓ := 0) rfl ha) := by
  rintro ⟨a, ha, eq⟩
  rw [state_repr] at eq
  have obs := pair_join_same (observation := plain) rfl rfl ((ofRegion_eq_iff Seed _ _).1 eq)
  have ol := obs envLeft typedLeft
  have or := obs envRight typedRight
  change Result.jump 0 (.inl .unit) = evalRegionWith plain (.br 0 a) envLeft at ol
  change Result.jump 0 (.inr .unit) = evalRegionWith plain (.br 0 a) envRight at or
  cases ha with
  | var hi =>
    rename_i i
    cases i with
    | zero => cases Option.some.inj hi
    | succ i => simp [At] at hi
  | inl hp => exact inl_ne_right _ _ or.symm
  | inr hp => exact inr_ne_left _ _ ol.symm

section Native

local notation "P" => Paper.TypeCategory.ofType (Φ := Empty)
local notation "PU" => P TyUnit
local notation "PD" => P Bit
local notation "F" => projection Seed

theorem native_state_constructor : Paper.TypeCategory.ConstructorReturn nativeState :=
  ⟨.inl (.var 0), .inl (.var (i := 0) rfl), Paper.TypeCategory.sumCofan_inl TyUnit TyUnit⟩

private theorem source_composite :
    nativeSource ≫ coprod.map (𝟙 PU) nativeState =
      Paper.TypeCategory.discardArrow TyUnit ≫ coprod.inl := by
  simp only [nativeSource, Category.assoc, coprod.inl_map, Category.id_comp]

private theorem target_composite : nativeState ≫ nativeTarget = (coprod.inl : PU ⟶ PU ⨿ PD) := by
  let collapse : PD ⟶ PU := (Paper.TypeCategory.sumCofanIsColimit TyUnit TyUnit).desc
    (BinaryCofan.mk (𝟙 PU) (𝟙 PU))
  change nativeState ≫ collapse ≫ (coprod.inl : PU ⟶ PU ⨿ PD) = coprod.inl
  have leg : nativeState ≫ collapse = 𝟙 PU :=
    (Paper.TypeCategory.sumCofanIsColimit TyUnit TyUnit).fac
      (BinaryCofan.mk (𝟙 PU) (𝟙 PU)) ⟨WalkingPair.left⟩
  rw [← Category.assoc nativeState collapse, leg, Category.id_comp]

theorem projected_native_square :
    projectStep Seed nativeSource ≫ coprod.map (𝟙 ((F).obj PU)) ((F).map nativeState) =
      (F).map nativeState ≫ projectStep Seed nativeTarget := by
  apply (projectSquare_iff Seed nativeSource nativeTarget nativeState).2
  rw [source_composite, target_composite, (F).map_comp,
    unit_eta_of_include Seed (Paper.WithPairReturns.StructuralValues.unitEta false).out, Category.id_comp]

theorem native_square_repair :
    ∃ f : PU ⟶ PU ⨿ PU, projectStep Seed f = projectStep Seed nativeSource ∧
      f ≫ coprod.map (𝟙 PU) nativeState = nativeState ≫ nativeTarget := by
  refine ⟨coprod.inl, ?_, ?_⟩
  · change (F).map (coprod.inl : PU ⟶ PU ⨿ PU) ≫ (PreservesColimitPair.iso (F) PU PU).inv =
      (F).map nativeSource ≫ (PreservesColimitPair.iso (F) PU PU).inv
    rw [nativeSource, (F).map_comp,
      unit_eta_of_include Seed (Paper.WithPairReturns.StructuralValues.unitEta false).out, Category.id_comp]
  · rw [target_composite, coprod.inl_map, Category.id_comp]

theorem native_square_ne :
    nativeSource ≫ coprod.map (𝟙 PU) nativeState ≠ nativeState ≫ nativeTarget := by
  rw [source_composite, target_composite]
  intro comm
  let collapse : PD ⟶ PU := (Paper.TypeCategory.sumCofanIsColimit TyUnit TyUnit).desc
    (BinaryCofan.mk (𝟙 PU) (𝟙 PU))
  have discard := congrArg (· ≫ coprod.desc (𝟙 PU) collapse) comm
  simp only [Category.assoc, coprod.inl_desc, Category.comp_id] at discard
  rw [← Paper.TypeCategory.ofRegion_id] at discard
  exact Paper.BoundSimulation.Obstruction.unit_eta_fails
    ((Paper.TypeCategory.ofRegion_eq_iff _ _).1 discard)

end Native

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedStructuralUniformity
