module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Blocks.ThreeCycle.PhaseProduct.Thms
public import Silmaril.Semantics.Calco2019.Maybe.Types.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Typed.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Semantics.Erasure.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Singleton.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Denotation.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.Product.Swap.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PhaseProductBit

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Semantics.Categorical
open Semantics.Interaction.Typed (AtomValues typeModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics (InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open Paper.SingletonReification (denoteSingleton_productFst)
open Paper.TypeCategory
open Paper.TypeCategory.PhaseProduct (payload Phase)
open CfgEta.TypeCategory (productFstBranches)
open CfgEta.TypeCategory.ConstructorReification (fstMap)
open scoped MonoidalCategory

universe u v
variable {κ : Type u} [AtomValues κ] {Φ : Type v} [HasTy Φ (Ty κ)]

local notation "U" => (Silmaril.unit : Ty κ)
local notation "Bit" => Silmaril.coprod U U
local notation "Input" => Silmaril.product Bit (Phase (τ := Ty κ))
local notation "Val" => Ty.denote (AtomValues.carrier (κ := κ))

set_option hygiene false in
set_option quotPrecheck false in
local notation "Maybe" => (Silmaril.Calco2019.Maybe.Types.Model : Type u → Type u)
local notation "M" => ofMonadicTypeModel (τ := Ty κ)
local notation "K" => typeJ (m := Maybe)

attribute [local instance] typeModel

local instance : HasEff Φ Bool := ⟨fun _ => true⟩

local instance : InstructionModel Φ (Ty κ) Bool Maybe where
  denote _ _ := .inr PUnit.unit
  denotePure _ h := by cases h
  denote_pure _ h := by cases h

local instance : Silmaril.Isotope.LetIter.Semantics.Categorical.InstructionModel K M Φ :=
  ofMonadicInstructionModel (ε := Bool)

local instance : RegionTypingCoherent (Φ := Φ) K M :=
  Semantics.Erasure.regionTypingCoherent (κ := κ) (Φ := Φ) (m := Maybe)
    (fun _ _ => .inr PUnit.unit) (.inr PUnit.unit) (.inr PUnit.unit)
    (fun _ _ => rfl)

omit [AtomValues κ] [HasTy Φ (Ty κ)] in
private theorem unit_value {a : Tm Φ} (ha : Tm.BranchValue [Input] a U) : a = .unit := by
  cases ha with
  | var h =>
    rename_i i
    cases i with
    | zero => cases h
    | succ i => simp [At] at h
  | unit => rfl

omit [AtomValues κ] [HasTy Φ (Ty κ)] in
private theorem bit_value {a : Tm Φ} (ha : Tm.BranchValue [Input] a Bit) :
    a = .inl .unit ∨ a = .inr .unit := by
  cases ha with
  | var h =>
    rename_i i
    cases i with
    | zero => cases h
    | succ i => simp [At] at h
  | inl h => exact .inl (congrArg Tm.inl (unit_value h))
  | inr h => exact .inr (congrArg Tm.inr (unit_value h))

set_option backward.isDefEq.respectTransparency false in
theorem no_constructor :
    ¬ ConstructorReturn (payload (Φ := Φ) Bit) := by
  rintro ⟨a, ha, eq⟩
  have observation := congrArg (denoteArrow K M) eq
  change denoteArrow K M (ofRegion (productFstBranches (Φ := Φ) Bit Phase)) = _ at observation
  rw [denoteArrow_ofRegion K M (fun _ _ => ⟨rfl, rfl⟩),
    denoteArrow_ofRegion K M (fun _ _ => ⟨rfl, rfl⟩), denoteSingleton_productFst] at observation
  let init : (M).obj Input ⟶ (M).obj U :=
    (λ_ ((M).obj Input)).inv ≫ SemiCartesianMonoidalCategory.toUnit (ctxObj M [Input]) ≫ (M).unitIso.inv
  let fst : (M).obj Input ⟶ (M).obj Bit := fstMap M Bit Phase
  have coordinates : ((M).coprodIso U U).inv = (Types.binaryCoproductIso ((M).obj U) ((M).obj U)).hom := by
    change (Types.binaryCoproductIso ((M).obj U) ((M).obj U)).hom ≫ 𝟙 ((M).obj Bit) = _
    exact Category.comp_id _
  rcases bit_value ha with rfl | rfl
  · rw [denoteSingletonRegion_br K M (.inl .unit)] at observation
    simp only [← Functor.map_comp, Category.assoc] at observation
    have eq' : (K).map fst = (K).map (init ≫
        coprod.inl ≫ ((M).coprodIso U U).inv) := by
      simpa only [fst, init, Category.assoc] using observation
    rw [coordinates] at eq'
    have wire := Types.binaryCoproductIso_inl_comp_hom ((M).obj U) ((M).obj U)
    have observed := eq'.trans (congrArg (fun k : (M).obj U ⟶ (M).obj Bit => (K).map (init ≫ k)) wire)
    have h := congrArg (fun f => f.of ((Sum.inr PUnit.unit, Sum.inl PUnit.unit) : Val Input)) observed
    change (Sum.inl (Sum.inr PUnit.unit) : Maybe (Val Bit)) = Sum.inl (Sum.inl _) at h
    cases Sum.inl.inj h
  · rw [denoteSingletonRegion_br K M (.inr .unit)] at observation
    simp only [← Functor.map_comp, Category.assoc] at observation
    have eq' : (K).map fst = (K).map (init ≫
        coprod.inr ≫ ((M).coprodIso U U).inv) := by
      simpa only [fst, init, Category.assoc] using observation
    rw [coordinates] at eq'
    have wire := Types.binaryCoproductIso_inr_comp_hom ((M).obj U) ((M).obj U)
    have observed := eq'.trans (congrArg (fun k : (M).obj U ⟶ (M).obj Bit => (K).map (init ≫ k)) wire)
    have h := congrArg (fun f => f.of ((Sum.inl PUnit.unit, Sum.inl PUnit.unit) : Val Input)) observed
    change (Sum.inl (Sum.inl PUnit.unit) : Maybe (Val Bit)) = Sum.inl (Sum.inr _) at h
    cases Sum.inl.inj h

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PhaseProductBit
