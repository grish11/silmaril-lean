module

import Silmaril.SSA.Isotope.LetIter.Categorical.Empty.Thms
import all Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.Empty.Reflection

open CategoryTheory CategoryTheory.Limits
open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical.AbortCounterexample
open Silmaril.Thesis.LambdaIter.LocallyNameless.Syntax

local instance : Silmaril.HasTy Bool (Ty Empty) where
  src _ := .unit
  trg _ := .empty

local instance : Silmaril.HasEff Bool Bool where
  eff _ := true

local instance : Silmaril.Thesis.LambdaIter.TypeFormers (Ty Empty) := S.formers
local instance : Silmaril.Thesis.LambdaIter.HasTy Bool (Ty Empty) := S.hasTy
local instance : Silmaril.Thesis.LambdaIter.HasEff Bool Bool := S.hasEff

theorem native_abort_equation_undervivable :
    ¬ LetIter.LocallyNameless.Equiv false (Ctx.nil : Ctx Empty (Ty Empty)) .nil
      (.abort (.op true .unit)) (.let₁ (.op true .unit) (.abort (.bv 0))) (Ty.unit : Ty Empty) := by
  intro h
  exact abort_equation_unprovable ((Bridge.equiv_iff (Bridge.TypeCompat.canonical (Ty Empty))
    (Bridge.InstrCompat.canonical Bool (Ty Empty)) (Bridge.EffCompat.canonical Bool Bool) false).mp h)

universe u₁ u₂ v₁ v₂
variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]
  (M : TypeModel (Ty Empty) V) [InstructionModel J M Bool]

theorem native_abort_equation_valid_in_every_central_unit_model :
    denote J M (.abort (C := Ty.unit) nativeScrutinee) =
    denote J M (.let₁ nativeScrutinee (.abort (C := Ty.unit) (.bv (ι := 0)))) :=
  (denote_let_abort J M nativeScrutinee Ty.unit).symm

#print axioms native_abort_equation_undervivable
#print axioms native_abort_equation_valid_in_every_central_unit_model
