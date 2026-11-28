module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Tripling.Components.Example.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Denotation.Preservation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Typed.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Semantics.Erasure.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Singleton.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithUnitEta.Thms
public import Silmaril.Semantics.Calco2019.Maybe.Types.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.MixedBitTriplingExample

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Semantics.Categorical
open Semantics.Interaction.Typed (AtomValues typeModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics (InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open Paper.TypeCategory.ComponentTripling.Example
open Paper.Extension.Singleton
open Paper.Extension.Singleton.Generation (primitive)

local instance : AtomValues Empty := ⟨Empty.elim⟩
attribute [local instance] typeModel

set_option hygiene false in
set_option quotPrecheck false in
local notation "Maybe" => (Silmaril.Calco2019.Maybe.Types.Model : Type → Type)
local notation "K" => typeJ (m := Maybe)
local notation "M" => ofMonadicTypeModel (τ := Ty Empty)
local notation "Val" => Ty.denote (AtomValues.carrier (κ := Empty))

def flipBit : Val Bit → Maybe (Val Reply)
  | .inl _ => .inl (.inr (.inr PUnit.unit))
  | .inr _ => .inl (.inr (.inl PUnit.unit))

local instance : InstructionModel Op (Ty Empty) Bool Maybe where
  denote p := match p with | .poll => flipBit
  denotePure p h := by cases p; cases h
  denote_pure p h _ := by cases p; cases h

local instance : Silmaril.Isotope.LetIter.Semantics.Categorical.InstructionModel K M Op :=
  ofMonadicInstructionModel (ε := Bool)

def rawFlip (_ : Op) : Value (Sigma (AtomValues.carrier (κ := Empty))) →
    Maybe (Value (Sigma (AtomValues.carrier (κ := Empty))))
  | .inl _ => .inl (.inr (.inr .unit))
  | .inr _ => .inl (.inr (.inl .unit))
  | _ => .inr PUnit.unit

local instance : RegionTypingCoherent (Φ := Op) K M :=
  Semantics.Erasure.regionTypingCoherent (κ := Empty) (Φ := Op) (m := Maybe)
    rawFlip (.inr PUnit.unit) (.inr PUnit.unit)
    (fun p x => by cases p; cases x <;> rfl)

private theorem sound : SeedDenotes (Seed := Seed) K M :=
  fun law hr hs => Paper.WithUnitEta.Step.denotes K M law hr hs

private theorem shared (X Y : Type) : ∃ h : (K).obj X ⊗ (K).obj Y = (K).obj (X ⊗ Y),
    Functor.StrongPremonoidal.tensorIso (J := K) X Y = eqToIso h :=
  ⟨rfl, rfl⟩

local notation "F" => denoteFunctor K M shared sound

set_option backward.isDefEq.respectTransparency false in
private theorem onRequest (x : Val Bit) : ((F).map (primitive Seed Op.poll)).of x = flipBit x := by
  have h := denoteFunctor_map_primitive K M shared sound Op.poll
  change 𝟙 _ ≫ (F).map (primitive Seed Op.poll) ≫ 𝟙 _ = _ at h
  rw [Category.comp_id, Category.id_comp] at h
  exact congrArg (fun a => a.of x) h

set_option backward.isDefEq.respectTransparency false in
private theorem onInl (A : Ty Empty) (x : Val U) :
    ((F).map (sumCofan Seed U A).inl).of x = .inl (.inl x) := by
  change ((F).map ((projection Seed).map (Paper.TypeCategory.sumCofan U A).inl)).of x = _
  rw [Paper.TypeCategory.sumCofan_inl, denoteFunctor_map_ofRegion K M shared sound,
    denoteSingletonRegion_br K M (.inl (.var (i := 0) rfl))]
  simp only [lookup, ← Functor.map_comp]
  change ((K).map (coprod.inl ≫ ((M).coprodIso U A).inv)).of x = _
  have coord : ((M).coprodIso U A).inv =
      (Types.binaryCoproductIso ((M).obj U) ((M).obj A)).hom := by
    change (Types.binaryCoproductIso ((M).obj U) ((M).obj A)).hom ≫ 𝟙 _ = _
    exact Category.comp_id _
  rw [coord, Types.binaryCoproductIso_inl_comp_hom]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem no_unit_factor (first : Obj Bit ⟶ Obj U ⨿ Obj U) (restore : Obj U ⟶ Obj Bit) :
    round ≠ first ≫ coprod.map (𝟙 (Obj U)) restore := by
  intro h
  let exactFirst : Obj Bit ⟶ Obj Bit := first ≫ (sumIso Seed U U).inv
  let route : Obj Bit ⟶ Obj Reply := (sumIso Seed U U).hom ≫ coprod.map (𝟙 (Obj U)) restore ≫ (sumIso Seed U Bit).inv
  have exactEq : primitive Seed Op.poll = exactFirst ≫ route := by
    calc
      _ = round ≫ (sumIso Seed U Bit).inv := by simp [round]
      _ = _ := by rw [h]; simp [exactFirst, route, Category.assoc]
  have keepExit : (sumCofan Seed U U).inl ≫ route = (sumCofan Seed U Bit).inl := by
    dsimp only [route]
    rw [← Category.assoc (sumCofan Seed U U).inl,
      sumCofan_inl_sumIso_hom, coprod.inl_map_assoc, Category.id_comp]
    rw [← sumCofan_inl_sumIso_hom (Seed := Seed) U Bit, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have exitOnLeft : ((F).map route).of (.inl PUnit.unit) = .inl (.inl PUnit.unit) := by
    have eq := congrArg (fun f : Obj U ⟶ Obj Reply => ((F).map f).of PUnit.unit) keepExit
    rw [Functor.map_comp, Kleisli.Type.comp_of_eq_kleisliRight, Bind.kleisliRight, onInl] at eq
    exact eq.trans (onInl Bit PUnit.unit)
  have endpoint (x : Val Bit) :
      flipBit x = Bind.bind (m := Maybe) (((F).map exactFirst).of x : Maybe (Val Bit))
        (fun y => ((F).map route).of y) := by
    have eq := congrArg (fun f : Obj Bit ⟶ Obj Reply => ((F).map f).of x) exactEq
    rw [Functor.map_comp, Kleisli.Type.comp_of_eq_kleisliRight, Bind.kleisliRight] at eq
    exact (onRequest x).symm.trans eq
  have recursive (x : Val Bit) : ((F).map exactFirst).of x = .inl (.inr PUnit.unit) := by
    have eq := endpoint x
    cases m : ((F).map exactFirst).of x with
    | inr aborted =>
      rw [m] at eq
      cases x <;> cases eq
    | inl reply =>
      cases reply with
      | inl u =>
        cases u
        rw [m] at eq
        change flipBit x = _ at eq
        have same : Bind.bind (m := Maybe) (Sum.inl (Sum.inl PUnit.unit) : Maybe (Val Bit))
            (fun y => ((F).map route).of y) = .inl (.inl PUnit.unit) := exitOnLeft
        have clash := eq.trans same
        cases x <;> cases Sum.inl.inj clash
      | inr u => cases u; rfl
  have l := endpoint (.inl PUnit.unit)
  have r := endpoint (.inr PUnit.unit)
  rw [recursive] at l r
  have contra := l.trans r.symm
  cases Sum.inr.inj (Sum.inl.inj contra)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.MixedBitTriplingExample
