module

public import Silmaril.Formats.Parquet.FlatColumn.Window.Defs
import Silmaril.Proofs.Formats.Parquet.FlatColumn.Window.Correctness

/-! Exact successful slices, unchanged full-column errors, and same-file index evidence. -/

public section

namespace Silmaril.Formats.Parquet.FlatColumn.Window

/-- The complete column determines the terminal error for every window. -/
theorem read_error_iff
    {snapshot : Snapshot.Checked} {selection : Selection} {α ε : Type}
    {binding : Binding snapshot selection} {limits : Limits} {policy : Policy}
    {decode : DecodePage α ε} {indexLimits : OffsetIndex.Limits}
    {group first stop : Nat} {error : Error ε} :
    Window.read binding limits policy decode indexLimits group first stop = .error error ↔
      readColumn binding limits policy decode group = .error error :=
  Proofs.Formats.Parquet.FlatColumn.Window.read_error_iff

/-- Observing only rows gives the clipped slice of the complete read. -/
theorem read_rows
    {snapshot : Snapshot.Checked} {selection : Selection} {α ε : Type}
    (binding : Binding snapshot selection) (limits : Limits) (policy : Policy)
    (decode : DecodePage α ε) (indexLimits : OffsetIndex.Limits) (group first stop : Nat) :
    (Window.read binding limits policy decode indexLimits group first stop).map Result.rows =
      (readColumn binding limits policy decode group).map (sliceRows first stop) :=
  Proofs.Formats.Parquet.FlatColumn.Window.read_rows binding limits policy decode indexLimits group first stop

theorem read_ok_iff
    {snapshot : Snapshot.Checked} {selection : Selection} {α ε : Type}
    {binding : Binding snapshot selection} {limits : Limits} {policy : Policy}
    {decode : DecodePage α ε} {indexLimits : OffsetIndex.Limits}
    {group first stop : Nat} {result : Result α} :
    Window.read binding limits policy decode indexLimits group first stop = .ok result ↔
      ∃ slots, readColumn binding limits policy decode group = .ok slots ∧
        result.rows = sliceRows first stop slots ∧
        result.indexPlan = OffsetIndex.Window.planChecked { indexLimits with page := limits.framing }
          snapshot group binding.columnOrdinal first stop :=
  Proofs.Formats.Parquet.FlatColumn.Window.read_ok_iff

theorem read_length
    {snapshot : Snapshot.Checked} {selection : Selection} {α ε : Type}
    {binding : Binding snapshot selection} {limits : Limits} {policy : Policy}
    {decode : DecodePage α ε} {indexLimits : OffsetIndex.Limits}
    {group first stop : Nat} {result : Result α}
    (h : Window.read binding limits policy decode indexLimits group first stop = .ok result) :
    ∃ selected, snapshot.groupAt group = some selected ∧
      result.rows.length = min stop selected.numRows.toNat - first :=
  Proofs.Formats.Parquet.FlatColumn.Window.read_length h

/-- The plan belongs to the original selected chunk, and the complete list
of callback results follows those same frames in wire order. -/
theorem read_plan_sound
    {snapshot : Snapshot.Checked} {selection : Selection} {α ε : Type}
    {binding : Binding snapshot selection} {limits : Limits} {policy : Policy}
    {decode : DecodePage α ε} {indexLimits : OffsetIndex.Limits}
    {group first stop : Nat} {result : Result α} {clips : List OffsetIndex.Window.Clip}
    (h : Window.read binding limits policy decode indexLimits group first stop = .ok result)
    (planned : result.indexPlan = .ok (some clips)) :
    ∃ index selected column chunk bytes pages,
      OffsetIndex.Evidence { indexLimits with page := limits.framing } snapshot group binding.columnOrdinal
        index selected column chunk bytes ∧
      List.Forall₂ (CallbackWire decode binding.leaf column.metadata snapshot.bytes)
        (index.pages.map OffsetIndex.Entry.frame) pages ∧
      clips = OffsetIndex.Window.plan first stop index ∧
      result.rows = sliceRows first stop pages.flatten :=
  Proofs.Formats.Parquet.FlatColumn.Window.read_plan_sound h planned

end Silmaril.Formats.Parquet.FlatColumn.Window
