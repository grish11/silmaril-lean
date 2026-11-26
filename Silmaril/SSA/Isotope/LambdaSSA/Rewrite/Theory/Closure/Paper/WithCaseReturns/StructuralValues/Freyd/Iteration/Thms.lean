module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.StructuralValues.Freyd.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.StructuralValues.Freyd.Iteration.Thms

/-! # Guarded iteration strength for the case-return computation model -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.StructuralValues

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedCase.Chosen
  (projectedChosenDistributor)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "Seed" => JoinedStep (τ := τ) (Φ := Φ) pe
set_option hygiene false in
local notation "Comp" => TypeCategory (τ := τ) (Φ := Φ) pe

attribute [local instance] computationPremonoidal computationSymmetric computationDistributive

/-- The chosen-coproduct guarded iterator for the structural Freyd model's computations. -/
noncomputable abbrev guardedIteration : Iteration Comp :=
  Extension.Singleton.guardedIteration Seed

/-- The model's canonical left distributor is the projected guarded distributor with sum conversions. -/
theorem leftIso_eq_guarded (Z B A : Comp) :
    DistributiveTensor.leftIso Z B A = projectedChosenDistributor Seed Z.as B.as A.as :=
  Extension.Singleton.StructuralValues.leftIso_eq_guarded (Seed) Z B A

/-- The guarded iterator satisfies the exact strength field on the model's chosen coproducts. -/
theorem iterate_whiskerLeft (Z : Comp) {A B : Comp} (f : A ⟶ B ⨿ A) :
    letI := guardedIteration (τ := τ) (Φ := Φ) pe
    CategoryTheory.iterate ((Z ◁ f) ≫ DistributivePremonoidalCategory.leftInv Z B A) =
      Z ◁ CategoryTheory.iterate f :=
  Extension.Singleton.StructuralValues.iterate_whiskerLeft (Seed) Z f

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.StructuralValues
