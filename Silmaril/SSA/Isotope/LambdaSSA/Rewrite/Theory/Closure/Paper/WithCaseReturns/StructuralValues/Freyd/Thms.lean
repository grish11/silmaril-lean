module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.StructuralValues.Freyd.Defs
public import Silmaril.Semantics.Categories.Freyd.CentralUnit.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.StructuralValues.Freyd.Thms

/-! # The structural value inclusion is distributive Freyd -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.StructuralValues

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open scoped MonoidalCategory

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "Seed" => JoinedStep (τ := τ) (Φ := Φ) pe
set_option hygiene false in
local notation "Val" => ValueCategory (τ := τ) (Φ := Φ) pe
set_option hygiene false in
local notation "Comp" => TypeCategory (τ := τ) (Φ := Φ) pe
set_option hygiene false in
local notation "inc" => inclusion (τ := τ) (Φ := Φ) pe

attribute [local instance] valueCartesian valueBraided computationPremonoidal computationSymmetric

/-- Whiskering the exact value sum uses the guarded distributivity isomorphism. -/
noncomputable def whiskeredSumIsColimit (X A B : τ) :
    IsColimit (BinaryCofan.map (MonoidalCategory.tensorLeft (ofSyntaxType (Φ := Φ) pe X))
      (Extension.Singleton.StructuralValues.sum Seed A B)) :=
  Extension.Singleton.StructuralValues.whiskeredSumIsColimit Seed X A B

/-- Left tensor distributes over the chosen binary value coproduct. -/
theorem valueDistributive : DistributiveTensor Val :=
  Extension.Singleton.StructuralValues.valueDistributive Seed

/-- Computations have the existing guarded distributive tensor. -/
theorem computationDistributive : DistributivePremonoidalCategory Comp :=
  Extension.Singleton.StructuralValues.computationDistributive Seed

/-- The inclusion has identity unit and tensor comparisons. -/
@[instance_reducible] noncomputable def freyd : FreydCategory (inc) :=
  Extension.Singleton.StructuralValues.freyd Seed

attribute [local instance] valueDistributive computationDistributive

/-- The structural value inclusion preserves finite coproducts and is distributive Freyd. -/
@[expose, instance_reducible] noncomputable def distributiveFreyd : DistributiveFreydCategory (inc) where
  toFreydCategory := freyd pe
  preservesFiniteCoproducts := inferInstance

/-- The Freyd unit comparison is central. -/
theorem centralUnit :
    letI := freyd (τ := τ) (Φ := Φ) pe
    FreydCategory.CentralUnit (inc) :=
  Extension.Singleton.StructuralValues.centralUnit Seed

/-- The Freyd tensor comparison is induced by the literal equality of tensor objects. -/
theorem sharedTensor (X Y : Val) :
    letI := freyd (τ := τ) (Φ := Φ) pe
    ∃ h : (inc).obj X ⊗ (inc).obj Y = (inc).obj (X ⊗ Y),
      Functor.StrongPremonoidal.tensorIso (J := (inc)) X Y = eqToIso h :=
  Extension.Singleton.StructuralValues.sharedTensor Seed X Y

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.StructuralValues
