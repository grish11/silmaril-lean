module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.StructuralValues.Factorization.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.Denotation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Denotation.Preservation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Typed.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Semantics.Erasure.Thms
public import Silmaril.Semantics.Calco2019.Maybe.Types.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingProjectionSquare

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Paper.WithCaseReturns.BinaryFold.WithTripling (Step seedDenotes)
open Paper.WithCaseReturns.BinaryFold.WithTripling.ProjectionSquare
open Paper.Extension.Singleton
open Paper.Extension.Singleton.StructuralValues (HomProperty fst_mem)
open Semantics.Categorical
open Semantics.Interaction.Typed (AtomValues typeModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics (InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)

universe u v w
variable {κ : Type u} {Φ : Type v} [HasTy Φ (Ty κ)]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "T" => Step (τ := Ty κ) (Φ := Φ) pe
set_option hygiene false in
local notation "Obj" => ofType T
local notation "Bit" => (Silmaril.coprod (Silmaril.unit : Ty κ) Silmaril.unit)
local notation "Pair" => (Silmaril.product Bit Bit)

private theorem after_first :
    next pe ≫ first pe = pairArrows T (first pe ≫ second pe) (hidden pe) :=
  pairing_fst_of_discard T _ _ (snd_discard T Pair Bit)

theorem composite_square :
    sourceStep pe ≫ coprod.map (𝟙 (Obj Pair)) (first pe ≫ second pe) =
      (first pe ≫ second pe) ≫ targetStep pe := by
  have retain : (next (κ := κ) (Φ := Φ) pe ≫ first pe) ≫ second pe = first pe ≫ second pe := by
    rw [after_first]
    exact pairing_fst_of_discard T _ _ (snd_discard T Pair Bit)
  simpa only [sourceStep, targetStep, Category.assoc, coprod.inr_map] using
    congrArg (· ≫ (coprod.inr : Obj Bit ⟶ Obj Pair ⨿ Obj Bit)) retain

private theorem after_hidden :
    (next pe ≫ first pe) ≫ productSnd T Bit Bit = hidden pe := by
  rw [after_first]
  exact pairing_snd_of_discard T _ _ ((HomProperty T).comp_mem _ _
    (fst_mem T Pair Bit) (fst_mem T Bit Bit)).2

local instance : AtomValues κ := ⟨fun _ => PUnit⟩
attribute [local instance] typeModel

set_option hygiene false in
set_option quotPrecheck false in
local notation "Maybe" => (Silmaril.Calco2019.Maybe.Types.Model : Type u → Type u)
local notation "M" => ofMonadicTypeModel (τ := Ty κ)
local notation "K" => typeJ (m := Maybe)

local instance : HasEff Φ Bool where
  eff _ := true

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

private theorem shared (X Y : Type u) :
    ∃ h : (K).obj X ⊗ (K).obj Y = (K).obj (X ⊗ Y),
      Functor.StrongPremonoidal.tensorIso (J := K) X Y = eqToIso h :=
  ⟨rfl, rfl⟩

set_option hygiene false in
local notation "Sound" => seedDenotes (Φ := Φ) pe K M shared
set_option hygiene false in
local notation "F" => denoteFunctor K M shared Sound

set_option backward.isDefEq.respectTransparency false in
private theorem hidden_not_factor (u : Obj Pair ⟶ Obj Bit) :
    hidden pe ≠ first pe ≫ u := by
  intro factor
  let model := Generation.Coordinates.ofModel K M
  have laws := denoteFunctor_preserves K M shared Sound
  have firstMap : (F).map (first pe) = model.fst Pair Bit := by
    have eq := laws.fst Pair Bit
    change 𝟙 _ ≫ (F).map (first pe) ≫ 𝟙 _ = model.fst Pair Bit at eq
    rwa [Category.id_comp, Category.comp_id] at eq
  have hiddenMap : (F).map (hidden pe) = model.snd Pair Bit := by
    have eq := laws.snd Pair Bit
    change 𝟙 _ ≫ (F).map (hidden pe) ≫ 𝟙 _ = model.snd Pair Bit at eq
    rwa [Category.id_comp, Category.comp_id] at eq
  have mapped : model.snd Pair Bit = model.fst Pair Bit ≫ (F).map u := calc
    _ = (F).map (hidden pe) := hiddenMap.symm
    _ = (F).map (first pe ≫ u) := congrArg (F).map factor
    _ = _ := ((F).map_comp _ _).trans (congrArg (· ≫ (F).map u) firstMap)
  let zero : (M).obj Bit := Sum.inl PUnit.unit
  let one : (M).obj Bit := Sum.inr PUnit.unit
  let input : (M).obj Pair := (zero, zero)
  have left := congrArg (fun g => g.of (input, zero)) mapped
  have right := congrArg (fun g => g.of (input, one)) mapped
  change (Sum.inl zero : Maybe ((M).obj Bit)) = ((F).map u).of input at left
  change (Sum.inl one : Maybe ((M).obj Bit)) = ((F).map u).of input at right
  have tags := Sum.inl.inj (left.trans right.symm)
  change (Sum.inl PUnit.unit : PUnit.{u + 1} ⊕ PUnit.{u + 1}) = Sum.inr PUnit.unit at tags
  cases tags

theorem no_intermediate_left (m : Obj Pair ⟶ Obj Pair ⨿ Obj Pair) :
    sourceStep pe ≫ coprod.map (𝟙 (Obj Pair)) (first pe) ≠ first pe ≫ m := by
  intro square
  let forgetExit : Obj Pair ⨿ Obj Pair ⟶ Obj Bit :=
    coprod.desc (productSnd T Bit Bit) (productSnd T Bit Bit)
  apply hidden_not_factor pe (m ≫ forgetExit)
  have out := congrArg (· ≫ forgetExit) square
  simp only [sourceStep, Category.assoc, coprod.inr_map_assoc, forgetExit, coprod.inr_desc] at out
  rw [← after_hidden pe]
  simpa only [Category.assoc] using out

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingProjectionSquare
