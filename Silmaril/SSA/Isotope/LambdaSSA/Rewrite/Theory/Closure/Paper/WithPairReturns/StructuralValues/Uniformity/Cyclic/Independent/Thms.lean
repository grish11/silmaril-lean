module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.IndependentUnitFold

/-! # Uniformity of the binary fold for independently rendered visible rows -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent

open CategoryTheory CategoryTheory.Limits
open Extension.Singleton (iterateChosen)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

local notation "U" => Cyclic.Visible.One
local notation "I" => iterateChosen Cyclic.Visible.Seed

/-- The actual quotient square recovers the complete finite reply trees after
erasing the destination copy. The observation distinguishes exit and recur. -/
theorem square_iff (left right : ReplyTree Route) (target : ReplyTree Bool) :
    sourceStep left right ≫ coprod.map (𝟙 U) fold = fold ≫ targetStep target ↔
      left.map Route.recurrent = target ∧ right.map Route.recurrent = target :=
  IndependentUnitFold.square_iff left right target

/-- The actual ordered-pair quotient square suffices for iteration equality.
Each row can choose its own destinations at arbitrary finite reply depth. -/
theorem uniformity (left right : ReplyTree Route) (target : ReplyTree Bool)
    (square : sourceStep left right ≫ coprod.map (𝟙 U) fold = fold ≫ targetStep target) :
    I (sourceStep left right) = fold ≫ I (targetStep target) :=
  IndependentUnitFold.uniformity left right target square

/-- Eliminating the second copy and then the first gives the same iteration
as the folded row. Here the quotient square discharges the mixed identity. -/
theorem mixed_identity (left right : ReplyTree Route) (target : ReplyTree Bool)
    (square : sourceStep left right ≫ coprod.map (𝟙 U) fold = fold ≫ targetStep target) :
    let a := sourceStep left right ≫ (coprod.associator U U U).inv
    I ((coprod.inl ≫ a) ≫ coprod.desc (𝟙 (U ⨿ U)) (I (coprod.inr ≫ a))) = I (targetStep target) :=
  IndependentUnitFold.mixed_identity left right target square

theorem fixture_square :
    sourceStep fixtureLeft fixtureRight ≫ coprod.map (𝟙 U) fold = fold ≫ targetStep fixtureTarget :=
  (square_iff _ _ _).2 ⟨rfl, rfl⟩

theorem fixture_iteration :
    I (sourceStep fixtureLeft fixtureRight) = fold ≫ I (targetStep fixtureTarget) :=
  uniformity _ _ _ fixture_square

/-- This fixture is outside the common decision with swapped destinations,
even as a quotient arrow. -/
theorem fixture_no_swap :
    ¬ ∃ decision : U ⟶ U ⨿ (U ⨿ U),
      sourceStep fixtureLeft fixtureRight = coprod.desc decision
        (decision ≫ coprod.map (𝟙 U) (coprod.desc coprod.inr coprod.inl)) :=
  IndependentUnitFold.fixture_no_swap

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent
