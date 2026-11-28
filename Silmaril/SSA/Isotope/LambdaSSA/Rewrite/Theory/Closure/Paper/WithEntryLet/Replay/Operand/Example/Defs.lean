module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Replay.Operand.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.EntryLet.Obstruction.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.CartesianBoundary.Thms

/-! # A cyclic square that forgets a two-tag state -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithEntryLet.OperandExample

open CategoryTheory CategoryTheory.Limits
open EntryLetObstruction
open SequencingObstruction (Instruction)
open Paper.TypeCategory (ofType ofRegion discardArrow sumIso sumCofan)

abbrev Seed := Step (τ := Ty Empty) (Φ := Instruction)
abbrev Bit : Ty Empty := Silmaril.coprod U U
abbrev X := ofType (Φ := Instruction) U
abbrev D := ofType (Φ := Instruction) Bit

/-- Forget either tag by returning the Unit constructor. -/
def forget : D ⟶ X := discardArrow Bit

theorem flatStep_typed : ValueBranches [U] flatRecurringRequest [Bit] :=
  CfgEta.TypeCategory.seqValueBranches flatRequest_typed (.br rfl (.inr .unit))

theorem movedStep_typed : ValueBranches [U] movedRecurringRequest [Bit] :=
  CfgEta.TypeCategory.seqValueBranches movedRequest_typed (.br rfl (.inr .unit))

/-- Run the supplied computation on either tag and recur with that tag. -/
noncomputable def taggedSource (run : X ⟶ X) : D ⟶ X ⨿ D :=
  let arm (inject : X ⟶ D) := discardArrow U ≫ run ≫
    discardArrow U ≫ inject ≫ (coprod.inr : D ⟶ X ⨿ D)
  (sumIso U U).hom ≫ coprod.desc (arm (sumCofan U U).inl) (arm (sumCofan U U).inr)

noncomputable def source : D ⟶ X ⨿ D := taggedSource (ofRegion movedRequest_typed)

/-- The written target still has the request inside its flat table. -/
noncomputable def target : X ⟶ X ⨿ X := ofRegion flatStep_typed ≫ (sumIso U U).hom

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithEntryLet.OperandExample
