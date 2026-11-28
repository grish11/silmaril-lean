module

public import Silmaril.Formats.Parquet.Int96.File.Defs
import all Silmaril.Formats.Parquet.Int96.File.Defs
import Silmaril.Formats.Parquet.FlatColumn.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Int96.File

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Int96 Silmaril.Formats.Parquet.Int96.File

variable {name : String} {layout : FlatColumn.Layout} {interpretation : Policy}

theorem openFile_sound {limits : Limits} {source : Bytes} {checked : Checked name layout interpretation}
    (opened : openFile limits source name layout interpretation = .ok checked) :
    source.length ≤ limits.maxFileBytes ∧
      Snapshot.check (Failure := Unit) limits.snapshot source = .ok checked.snapshot ∧
      checked.snapshot.metadata.numRows.toNat ≤ limits.maxTotalRows ∧
      FlatColumn.bindColumn checked.snapshot ⟨name, .int96, layout⟩ = .ok checked.binding ∧
      checked.columnLimits = limits.column := by
  by_cases bytes : limits.maxFileBytes < source.length
  · simp [openFile, bytes, Bind.bind, Except.bind] at opened
  · cases parsed : Snapshot.check (Failure := Unit) limits.snapshot source with
    | error reason =>
      simp [openFile, bytes, parsed, Bind.bind, Except.bind, Except.mapError] at opened
    | ok snapshot =>
      by_cases rows : limits.maxTotalRows < snapshot.metadata.numRows.toNat
      · simp [openFile, bytes, parsed, rows, Bind.bind, Except.bind, Except.mapError] at opened
      · cases bound : FlatColumn.bindColumn snapshot ⟨name, .int96, layout⟩ with
        | error reason =>
          simp [openFile, bytes, parsed, rows, bound, Bind.bind, Except.bind, Except.mapError] at opened
        | ok binding =>
          simp [openFile, bytes, parsed, rows, bound, Bind.bind, Except.bind, Except.mapError,
            Pure.pure, Except.pure] at opened
          subst checked
          exact ⟨Nat.le_of_not_gt bytes, rfl, Nat.le_of_not_gt rows, bound, rfl⟩

theorem readGroup_wire {checked : Checked name layout interpretation} {index : Nat}
    {slots : Slots interpretation} (read : checked.readGroup index = .ok slots) :
    ∃ group, FlatColumn.ColumnWire checked.binding checked.columnLimits
      (decodePage interpretation checked.columnLimits) index group slots :=
  FlatColumn.readColumn_wire read

private theorem loop_sound (checked : Checked name layout interpretation)
    (indices : List Nat) (reversed : List (Slots interpretation)) :
    let trace := Checked.readAll.loop checked indices reversed
    ∃ completed, trace.groups = reversed.reverse ++ completed ∧
      match trace.failure with
      | none => indices.mapM checked.readGroup = .ok completed
      | some cause =>
        ∃ before index after, indices = before ++ index :: after ∧
          before.mapM checked.readGroup = .ok completed ∧ checked.readGroup index = .error cause := by
  induction indices generalizing reversed with
  | nil => exact ⟨[], by simp [Checked.readAll.loop], rfl⟩
  | cons index rest ih =>
    simp only [Checked.readAll.loop]
    cases first : checked.readGroup index with
    | error cause =>
      exact ⟨[], by simp, [], index, rest, rfl, rfl, first⟩
    | ok slots =>
      obtain ⟨completed, ordered, outcome⟩ := ih (slots :: reversed)
      refine ⟨slots :: completed, ?_, ?_⟩
      · simpa [List.reverse_cons, List.append_assoc] using ordered
      · cases failed : (Checked.readAll.loop checked rest (slots :: reversed)).failure with
        | none =>
          simp only [failed] at outcome ⊢
          simp [List.mapM_cons, first, outcome, Bind.bind, Except.bind, Pure.pure, Except.pure]
        | some cause =>
          simp only [failed] at outcome ⊢
          obtain ⟨before, bad, after, rfl, earlier, invalid⟩ := outcome
          refine ⟨index :: before, bad, after, rfl, ?_, invalid⟩
          simp [List.mapM_cons, first, earlier, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem readAll_sound (checked : Checked name layout interpretation) :
    let indices := List.range checked.snapshot.groupCount
    let trace := checked.readAll
    match trace.failure with
    | none => indices.mapM checked.readGroup = .ok trace.groups
    | some cause =>
      ∃ before index after, indices = before ++ index :: after ∧
        before.mapM checked.readGroup = .ok trace.groups ∧ checked.readGroup index = .error cause := by
  obtain ⟨completed, ordered, outcome⟩ := loop_sound checked (List.range checked.snapshot.groupCount) []
  simp only [List.reverse_nil, List.nil_append] at ordered
  cases failed : (Checked.readAll.loop checked (List.range checked.snapshot.groupCount) []).failure <;>
    simpa only [Checked.readAll, ordered, failed] using outcome

private theorem loop_after_prefix (checked : Checked name layout interpretation)
    {before : List Nat} {groups : List (Slots interpretation)}
    (earlier : before.mapM checked.readGroup = .ok groups) (after : List Nat)
    (reversed : List (Slots interpretation)) :
    Checked.readAll.loop checked (before ++ after) reversed =
      Checked.readAll.loop checked after (groups.reverse ++ reversed) := by
  induction before generalizing groups reversed with
  | nil =>
    simp [Pure.pure, Except.pure] at earlier
    subst groups
    rfl
  | cons index before ih =>
    cases first : checked.readGroup index with
    | error cause => simp [List.mapM_cons, first, Bind.bind, Except.bind] at earlier
    | ok slots =>
      cases tail : before.mapM checked.readGroup with
      | error cause => simp [List.mapM_cons, first, tail, Bind.bind, Except.bind] at earlier
      | ok remaining =>
        have allGroups : slots :: remaining = groups := by
          simpa [List.mapM_cons, first, tail, Bind.bind, Except.bind, Pure.pure, Except.pure] using earlier
        subst groups
        simpa [Checked.readAll.loop, first, List.reverse_cons, List.append_assoc] using
          ih tail (slots :: reversed)

theorem readAll_complete {checked : Checked name layout interpretation} {groups : List (Slots interpretation)}
    (decoded : (List.range checked.snapshot.groupCount).mapM checked.readGroup = .ok groups) :
    checked.readAll = ⟨groups, none⟩ := by
  have whole := loop_after_prefix checked decoded [] []
  simpa [Checked.readAll, Checked.readAll.loop] using whole

theorem readAll_first_error {checked : Checked name layout interpretation}
    {before after : List Nat} {index : Nat} {groups : List (Slots interpretation)} {cause : ReadError}
    (split : List.range checked.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM checked.readGroup = .ok groups)
    (failed : checked.readGroup index = .error cause) :
    checked.readAll = ⟨groups, some cause⟩ := by
  rw [Checked.readAll, split, loop_after_prefix checked earlier]
  simp [Checked.readAll.loop, failed]

end Silmaril.Proofs.Formats.Parquet.Int96.File
