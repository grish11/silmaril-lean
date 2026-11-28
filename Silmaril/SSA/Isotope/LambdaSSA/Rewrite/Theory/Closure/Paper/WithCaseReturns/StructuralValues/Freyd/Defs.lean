module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.StructuralValues.Freyd.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.StructuralValues.Thms

/-! # Chosen structures for the structural value inclusion -/

@[expose] public section

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
open Extension.Singleton.StructuralValues (IncludesUnitEta)

instance unitEta : Fact (IncludesUnitEta (Seed)) :=
  ⟨includeUnit pe⟩

/-- Cartesian products use the exact syntax product, and the unit uses unit η. -/
noncomputable abbrev valueCartesian : CartesianMonoidalCategory Val :=
  Extension.Singleton.StructuralValues.valueCartesian (Seed)

attribute [local instance] valueCartesian

/-- The value symmetry is induced by the Cartesian tensor. -/
noncomputable abbrev valueBraided : BraidedCategory Val :=
  Extension.Singleton.StructuralValues.valueBraided (Seed)

/-- Computations use the existing syntactic whiskers and unit-η coherence. -/
abbrev computationPremonoidal : PremonoidalCategory Comp :=
  Extension.Singleton.StructuralValues.computationPremonoidal (Seed)

abbrev computationSymmetric : @SymmetricPremonoidalCategory Comp _ (computationPremonoidal pe) :=
  Extension.Singleton.StructuralValues.computationSymmetric (Seed)

instance valueHasFiniteCoproducts : HasFiniteCoproducts Val :=
  Extension.Singleton.StructuralValues.hasFiniteCoproducts Seed

instance : PreservesFiniteCoproducts (inc) :=
  Extension.Singleton.StructuralValues.preservesFiniteCoproducts Seed

/-- Types are interpreted by their guarded syntax objects. -/
@[instance_reducible] noncomputable def typeModel : TypeModel τ Val :=
  Extension.Singleton.StructuralValues.typeModel (Seed)

/-- Primitive instructions have their direct guarded computation representatives. -/
@[instance_reducible] def instructions : InstructionModel (inc) (typeModel pe) Φ :=
  Extension.Singleton.StructuralValues.instructions (Seed)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.StructuralValues
