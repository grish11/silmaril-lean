module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.StructuralValues.Uniformity.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Acyclic.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Uniformity.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedStructuralUniformity

/-! # Native replay and acyclic uniformity in the ordered-pair join -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.StructuralValues.Uniformity

open Silmaril.Isotope.LambdaSSA
open CategoryTheory CategoryTheory.Limits
open scoped Paper.BoundSimulation.Obstruction
open Extension.Singleton
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

local notation "TyUnit" => Paper.WithPairReturns.StructuralValues.Uniformity.UnitTy
local notation "Obj" => ofType Seed
local notation "U" => Obj TyUnit
local notation "D" => Obj Bit
local notation "A" => Obj Three

/-- The fold preserves interchange, copying, and discard in the actual quotient. -/
theorem state_structural : Extension.Singleton.StructuralValues.HomProperty Seed stateMap :=
  JoinedStructuralUniformity.state_structural

/-- The fold identifies the lower state with the left tag in the upper stratum. -/
theorem state_not_mono : ¬ Mono stateMap :=
  JoinedStructuralUniformity.state_not_mono

/-- The structural fold has no branch-value representative at these exact types. -/
theorem no_constructor_state :
    ¬ ∃ (a : Tm Empty) (ha : Tm.BranchValue [Three] a Bit),
      stateMap = ofRegion Seed (.br (ℓ := 0) rfl ha) :=
  JoinedStructuralUniformity.no_constructor_state

/-- The two steps give a commuting square with the structural fold. -/
theorem joined_square :
    sourceStep ≫ coprod.map (𝟙 U) stateMap = stateMap ≫ targetStep :=
  JoinedStructuralUniformity.joined_square

/-- The source has two strata, with transfers from the upper stratum to the lower one. -/
theorem source_bounded : AcyclicStep Seed U sourceStep :=
  JoinedStructuralUniformity.source_bounded

/-- A right tag in the upper stratum takes the recursive exit. -/
theorem upper_right_transfer :
    (sumCofan Seed TyUnit TyUnit).inr ≫ (sumCofan Seed TyUnit Bit).inr ≫ sourceStep =
      (sumCofan Seed TyUnit Bit).inl ≫ (coprod.inr : A ⟶ U ⨿ A) :=
  JoinedStructuralUniformity.upper_right_transfer

/-- The actual square gives iteration equality for this finite stratification. -/
theorem joined_iteration :
    iterateChosen Seed sourceStep = stateMap ≫ iterateChosen Seed targetStep :=
  JoinedStructuralUniformity.joined_iteration

local notation "PU" => Paper.TypeCategory.ofType (Φ := Empty) TyUnit
local notation "F" => projection Seed

/-- The separate square-reflection fixture does have a constructor state map. -/
theorem native_state_constructor : Paper.TypeCategory.ConstructorReturn nativeState :=
  JoinedStructuralUniformity.native_state_constructor

/-- The projected square commutes by unit η in the ordered-pair join. -/
theorem projected_native_square :
    projectStep Seed nativeSource ≫ coprod.map (𝟙 ((F).obj PU)) ((F).map nativeState) =
      (F).map nativeState ≫ projectStep Seed nativeTarget :=
  JoinedStructuralUniformity.projected_native_square

/-- The fixed standard Paper representatives do not give the square required by native uniformity. -/
theorem native_square_ne :
    nativeSource ≫ coprod.map (𝟙 PU) nativeState ≠ nativeState ≫ nativeTarget :=
  JoinedStructuralUniformity.native_square_ne

/-- Choosing a different source representative recovers a native square in this example. -/
theorem native_square_repair :
    ∃ f : PU ⟶ PU ⨿ PU, projectStep Seed f = projectStep Seed nativeSource ∧
      f ≫ coprod.map (𝟙 PU) nativeState = nativeState ≫ nativeTarget :=
  JoinedStructuralUniformity.native_square_repair

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.StructuralValues.Uniformity
