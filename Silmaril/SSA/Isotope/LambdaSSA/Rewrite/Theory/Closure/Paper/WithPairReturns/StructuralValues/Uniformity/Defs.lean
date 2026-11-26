module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.StructuralValues.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Acyclic.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Obstruction.Defs

/-! # Ordered-pair feedback examples at the native replay boundary -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.StructuralValues.Uniformity

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open CategoryTheory CategoryTheory.Limits
open scoped Paper.BoundSimulation.Obstruction
open Extension.Singleton (ofType sumIso sumCofan)
open Extension.Singleton.ValueCoproducts (exactCopair)

scoped instance : HasEff Empty Bool := ⟨Empty.elim⟩

abbrev Seed := JoinedStep (τ := Ty Empty) (Φ := Empty) false
abbrev UnitTy : Ty Empty := Silmaril.unit
abbrev Bit := Silmaril.coprod UnitTy UnitTy
abbrev Three := Silmaril.coprod UnitTy Bit

local notation "Obj" => ofType Seed
local notation "U" => Obj UnitTy
local notation "D" => Obj Bit
local notation "A" => Obj Three

abbrev tag : U ⟶ D := (sumCofan Seed UnitTy UnitTy).inl

/-- Fold the extra left state onto the left tag and preserve both tags of the right summand. -/
noncomputable def stateMap : A ⟶ D :=
  exactCopair Seed tag (𝟙 D)

/-- The two upper tags select an exit or a transfer to the lower stratum. -/
noncomputable abbrev upperRow : D ⟶ U ⨿ U := (sumIso Seed UnitTy UnitTy).hom

/-- The lower stratum exits. A right-tagged input in the upper stratum transfers to the lower stratum. -/
noncomputable def sourceStep : A ⟶ U ⨿ A :=
  let split := sumIso Seed UnitTy Bit
  split.hom ≫ coprod.desc coprod.inl upperRow ≫ coprod.map (𝟙 U) (coprod.inl ≫ split.inv)

/-- The target transfers from the right tag to the left tag and then exits. -/
noncomputable def targetStep : D ⟶ U ⨿ D :=
  upperRow ≫ coprod.map (𝟙 U) tag

section Native

local notation "P" => Paper.TypeCategory.ofType (Φ := Empty)
local notation "PU" => P UnitTy
local notation "PD" => P Bit

/-- A constructor state map used to test whether the equality of fixed representatives reflects. -/
def nativeState : PU ⟶ PD := (Paper.TypeCategory.sumCofan UnitTy UnitTy).inl

/-- Exit directly with the literal unit. -/
noncomputable def nativeSource : PU ⟶ PU ⨿ PU :=
  Paper.TypeCategory.discardArrow UnitTy ≫ coprod.inl

/-- Exit with the unit payload from either tag. -/
noncomputable def nativeTarget : PD ⟶ PU ⨿ PD :=
  (Paper.TypeCategory.sumCofanIsColimit UnitTy UnitTy).desc (BinaryCofan.mk (𝟙 PU) (𝟙 PU)) ≫ coprod.inl

end Native

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.StructuralValues.Uniformity
