module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Comparison.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Replay.Operand.Example.Thms

/-! # Binary repair of a cyclic square that forgets a state tag -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.ReplayExample

open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory (ofRegion sumIso)
open Paper.EntryLetObstruction.Destructure
open Paper.WithEntryLet.OperandExample (Bit X D taggedSource)
open SequencingObstruction (Instruction)

abbrev Seed := Step (τ := Ty Empty) (Φ := Instruction)

abbrev forget : D ⟶ X := Paper.WithEntryLet.OperandExample.forget

/-- Same computed pair and same two transfers as the strictness witness. -/
theorem flat_typed : ValueBranches [U] original [U] :=
  .cfg labels (.let₂ (.pair (.op .unit) .unit) (.br (ℓ := 0) rfl (.var (i := 1) rfl)))
    Comparison.DestructureFixture.rows_typed

theorem moved_typed : ValueBranches [U] moved [U] :=
  .let₂ (.pair (.op .unit) .unit) (.cfg labels (.br (ℓ := 0) rfl (.var (i := 1) rfl))
    (fun j => ((Comparison.DestructureFixture.rows_typed j).renameVars ((Ren.wk _ _).lift (labels j)))
      |>.renameVars ((Ren.wk _ _).lift (labels j))))

theorem flatStep_typed : ValueBranches [U] (recurring original) [Bit] :=
  CfgEta.TypeCategory.seqValueBranches flat_typed (.br rfl (.inr .unit))

theorem movedStep_typed : ValueBranches [U] (recurring moved) [Bit] :=
  CfgEta.TypeCategory.seqValueBranches moved_typed (.br rfl (.inr .unit))

/-- Each source state runs the moved computation and repeats with its own tag. -/
noncomputable def source : D ⟶ X ⨿ D := taggedSource (ofRegion moved_typed)

/-- The target runs the flat table before taking a repeat edge. -/
noncomputable def target : X ⟶ X ⨿ X := ofRegion flatStep_typed ≫ (sumIso U U).hom

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.ReplayExample
