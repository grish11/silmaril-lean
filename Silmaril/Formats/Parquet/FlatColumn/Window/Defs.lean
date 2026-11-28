module

public import Silmaril.Formats.Parquet.FlatColumn.Defs
public import Silmaril.Formats.Parquet.OffsetIndex.Window.Defs

/-! Post-read row slicing with an independent checked index diagnostic. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.FlatColumn.Window

structure Result (α : Type) where
  rows : List (Option α)
  /-- A present plan, an absent index, or an index validation error, reported
  only after the selected column has been read successfully. -/
  indexPlan : Except OffsetIndex.Error (Option (List OffsetIndex.Window.Clip))

/-- A zero-based, half-open window clipped to the available rows. -/
def sliceRows {α : Type} (first stop : Nat) (rows : List α) : List α :=
  (rows.drop first).take (stop - first)

/-- Read the entire selected column under its existing limits and policy.
The outer error is the original column error. Only after success do we
slice the rows and check the index using the reader's framing limits
and the caller's remaining index limits. -/
def read {snapshot : Snapshot.Checked} {selection : Selection} {α ε : Type}
    (binding : Binding snapshot selection) (limits : Limits) (policy : Policy)
    (decode : DecodePage α ε) (indexLimits : OffsetIndex.Limits)
    (group first stop : Nat) : Except (Error ε) (Result α) := do
  let slots ← readColumn binding limits policy decode group
  let indexPlan := OffsetIndex.Window.planChecked { indexLimits with page := limits.framing }
    snapshot group binding.columnOrdinal first stop
  pure ⟨sliceRows first stop slots, indexPlan⟩

end Silmaril.Formats.Parquet.FlatColumn.Window
