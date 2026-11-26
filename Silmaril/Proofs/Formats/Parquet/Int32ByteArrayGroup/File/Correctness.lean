module

public import Silmaril.Formats.Parquet.Int32ByteArrayGroup.File.Defs
import all Silmaril.Formats.Parquet.Int32ByteArrayGroup.File.Defs
import Silmaril.Formats.Parquet.Int32ByteArrayGroup.Thms
import Silmaril.Formats.Parquet.Reader.Thms
import Silmaril.Formats.Parquet.Snapshot.RowCounts.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Int32ByteArrayGroup.File

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Arrow
open Silmaril.Formats.Parquet.Int32ByteArrayGroup Silmaril.Formats.Parquet.Int32ByteArrayGroup.File
open Silmaril.Relational

private theorem bind_ok {ε α β : Type} {input : Except ε α} {f : α → Except ε β} {out : β}
    (success : (input >>= f) = .ok out) : ∃ a, input = .ok a ∧ f a = .ok out := by
  cases input with
  | error _ => cases success
  | ok a => exact ⟨a, rfl, success⟩

theorem openFile_snapshot {limits : File.Limits} {input : Bytes} {int32 byteArray : Field}
    {checked : File.Checked limits int32 byteArray}
    (opened : File.openFile limits input int32 byteArray = .ok checked) :
    Snapshot.check (Failure := Unit) limits.group.snapshot input = .ok checked.projection.snapshot ∧
    checked.projection.snapshot.metadata.numRows.toNat ≤ limits.maxFileRows := by
  refine ⟨?_, checked.rowCap⟩
  unfold File.openFile at opened
  obtain ⟨projection, projected, opened⟩ := bind_ok opened
  dsimp only at opened
  split at opened <;> try contradiction
  cases opened
  cases read : Int32ByteArrayGroup.openFile limits.group input int32 byteArray with
  | error _ => simp [read, Except.mapError] at projected
  | ok _ =>
    simp [read, Except.mapError] at projected
    cases projected
    exact (Int32ByteArrayGroup.openFile_snapshot read).1

theorem openFile_rowLimit {limits : File.Limits} {input : Bytes} {int32 byteArray : Field}
    {projection : Int32ByteArrayGroup.Checked int32 byteArray}
    (opened : Int32ByteArrayGroup.openFile limits.group input int32 byteArray = .ok projection)
    (over : limits.maxFileRows < projection.snapshot.metadata.numRows.toNat) :
    File.openFile limits input int32 byteArray =
      .error (.fileRowLimit limits.maxFileRows projection.snapshot.metadata.numRows.toNat) := by
  unfold File.openFile
  rw [opened]
  change (if admitted : projection.snapshot.metadata.numRows.toNat ≤ limits.maxFileRows
    then (Except.ok ⟨projection, admitted⟩ : Except File.Error (File.Checked limits int32 byteArray))
    else Except.error (.fileRowLimit limits.maxFileRows projection.snapshot.metadata.numRows.toNat)) = _
  exact dite_eq_right (Nat.not_le_of_gt over)

theorem batch_projections (int32 byteArray : Field) (pairs : List Int32ByteArrayGroup.Row) :
    let batch := AlignedColumns.ofRows (File.rows int32 byteArray pairs)
    batch.rowCount = pairs.length ∧
    batch.values ⟨0, by change 0 < 2; decide⟩ = pairs.map Prod.fst ∧
    batch.values ⟨1, by change 1 < 2; decide⟩ = pairs.map Prod.snd := by
  simp only [AlignedColumns.ofRows, File.rows, List.length_map, List.map_map, true_and]
  exact ⟨rfl, rfl⟩

private theorem denote_append_success {limits : File.Limits} {int32 byteArray : Field}
    (checked : File.Checked limits int32 byteArray) (before after : List Nat)
    {groups : List (List Int32ByteArrayGroup.Row)}
    (decoded : before.mapM (checked.projection.readGroup limits.group) = .ok groups) :
    let tail := Reader.denoteGroups checked.source.readGroup after
    Reader.denoteGroups checked.source.readGroup (before ++ after) =
      (groups.map (File.rows int32 byteArray) ++ tail.1, tail.2) := by
  induction before generalizing groups with
  | nil =>
    cases decoded
    rfl
  | cons index rest ih =>
    rw [List.mapM_cons] at decoded
    obtain ⟨pairs, read, decoded⟩ := bind_ok decoded
    obtain ⟨following, reads, decoded⟩ := bind_ok decoded
    cases decoded
    have first : checked.source.readGroup index = .ok (File.rows int32 byteArray pairs) := by
      simp [File.Checked.source, read, Except.map, Except.mapError]
    simp [Reader.denoteGroups, first, ih reads]

theorem readAll_success {limits : File.Limits} {input : Bytes} {int32 byteArray : Field}
    {checked : File.Checked limits int32 byteArray} {groups : List (List Int32ByteArrayGroup.Row)}
    (opened : File.openFile limits input int32 byteArray = .ok checked)
    (decoded : (List.range checked.projection.snapshot.groupCount).mapM
      (checked.projection.readGroup limits.group) = .ok groups) :
    Reader.readAll (File.openSource limits input int32 byteArray) = .ok ⟨File.schema int32 byteArray,
      ⟨groups.map (AlignedColumns.ofRows ∘ File.rows int32 byteArray), .eos⟩⟩ := by
  have ordered := denote_append_success checked (List.range checked.projection.snapshot.groupCount) [] decoded
  simp only [List.append_nil, Reader.denoteGroups] at ordered
  have order : Reader.denoteGroups checked.source.readGroup checked.source.groups =
      (groups.map (File.rows int32 byteArray), .eos) := ordered
  rw [File.openSource, opened]
  change Reader.readAll (.ok ⟨File.schema int32 byteArray, checked.source⟩) = _
  rw [Reader.readAll_opened, order]
  simp only [List.map_map]

theorem readAll_first_error {limits : File.Limits} {input : Bytes} {int32 byteArray : Field}
    {checked : File.Checked limits int32 byteArray} {before after : List Nat} {index : Nat}
    {groups : List (List Int32ByteArrayGroup.Row)} {reason : Int32ByteArrayGroup.Error}
    (opened : File.openFile limits input int32 byteArray = .ok checked)
    (split : List.range checked.projection.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (checked.projection.readGroup limits.group) = .ok groups)
    (failed : checked.projection.readGroup limits.group index = .error reason) :
    Reader.readAll (File.openSource limits input int32 byteArray) = .ok ⟨File.schema int32 byteArray,
      ⟨groups.map (AlignedColumns.ofRows ∘ File.rows int32 byteArray), .readError (.groupFailure index reason)⟩⟩ := by
  have ordered := denote_append_success checked before (index :: after) earlier
  rw [← split] at ordered
  have order : Reader.denoteGroups checked.source.readGroup checked.source.groups =
      (groups.map (File.rows int32 byteArray), .readError (.groupFailure index reason)) := by
    calc
      _ = _ := ordered
      _ = _ := by simp [Reader.denoteGroups, File.Checked.source, failed, Except.map, Except.mapError]
  rw [File.openSource, opened]
  change Reader.readAll (.ok ⟨File.schema int32 byteArray, checked.source⟩) = _
  rw [Reader.readAll_opened, order]
  simp only [List.map_map]

private theorem denote_rows_le {limits : File.Limits} {int32 byteArray : Field}
    (checked : File.Checked limits int32 byteArray) (indices : List Nat) :
    ((Reader.denoteGroups checked.source.readGroup indices).1.map List.length).sum ≤
      (indices.map fun index => ((checked.projection.snapshot.groupAt index).map (·.numRows.toNat)).getD 0).sum := by
  induction indices with
  | nil => simp [Reader.denoteGroups]
  | cons index rest ih =>
    cases read : checked.projection.readGroup limits.group index with
    | error reason =>
      have failed : checked.source.readGroup index = .error (.groupFailure index reason) := by
        simp [File.Checked.source, read, Except.map, Except.mapError]
      simp [Reader.denoteGroups, failed]
    | ok pairs =>
      have success : checked.source.readGroup index = .ok (File.rows int32 byteArray pairs) := by
        simp [File.Checked.source, read, Except.map, Except.mapError]
      obtain ⟨group, _, _, wire, _, _, _, _, count, _, _⟩ := Int32ByteArrayGroup.readGroup_wire read
      obtain ⟨_, _, _, _, picked, _⟩ := wire
      have size : (File.rows int32 byteArray pairs).length = group.numRows.toNat := by
        simpa [File.rows] using count
      simp only [Reader.denoteGroups, success, List.map_cons, List.sum_cons, picked,
        Option.map_some, Option.getD_some, size]
      exact Nat.add_le_add_left ih _

theorem readAll_rows_le {limits : File.Limits} {input : Bytes} {int32 byteArray : Field}
    {selected : Scan.Schema String File.Kind} {trace : Events.Trace selected File.Value File.Error}
    (observed : Reader.readAll (File.openSource limits input int32 byteArray) = .ok ⟨selected, trace⟩) :
    (trace.batches.map (·.rowCount)).sum ≤ limits.maxFileRows := by
  cases opened : File.openFile limits input int32 byteArray with
  | error reason => simp [File.openSource, opened, Except.map, Reader.readAll] at observed
  | ok checked =>
    have cap := denote_rows_le checked (List.range checked.projection.snapshot.groupCount)
    have snapshot := openFile_snapshot opened
    rw [← Snapshot.check_rowCounts snapshot.1] at cap
    rw [File.openSource, opened] at observed
    change Reader.readAll (.ok ⟨File.schema int32 byteArray, checked.source⟩) = _ at observed
    rw [Reader.readAll_opened] at observed
    cases observed
    have groups : checked.source.groups = List.range checked.projection.snapshot.groupCount := rfl
    simpa only [List.map_map, Function.comp_def, AlignedColumns.ofRows, groups] using
      Nat.le_trans cap snapshot.2

end Silmaril.Proofs.Formats.Parquet.Int32ByteArrayGroup.File
