module

public import Silmaril.Formats.Parquet.Int32ByteArrayGroup.DeltaLength.File.Defs
import Silmaril.Formats.Parquet.Int32ByteArrayGroup.DeltaLength.Thms
import Silmaril.Formats.Parquet.Int32ByteArrayGroup.File.Thms
import Silmaril.Formats.Parquet.Reader.Thms
import Silmaril.Formats.Parquet.Snapshot.RowCounts.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Int32ByteArrayGroup.DeltaLength.File

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Arrow Silmaril.Relational
open Silmaril.Formats.Parquet.Int32ByteArrayGroup.DeltaLength.File

variable {limits : Limits} {input : Bytes} {int32Name byteArrayName : String}
variable {checked : Checked limits int32Name byteArrayName}

theorem openFile_snapshot (opened : openFile limits input int32Name byteArrayName = .ok checked) :
    Snapshot.check (Failure := Unit) limits.group.group.snapshot input = .ok checked.projection.snapshot ∧
    checked.projection.snapshot.metadata.numRows.toNat ≤ limits.maxFileRows := by
  unfold openFile at opened
  cases admitted : Int32ByteArrayGroup.File.openFile limits.admission input
      ⟨int32Name, .required⟩ ⟨byteArrayName, .optional⟩ with
  | error reason => simp [admitted, Except.mapError] at opened
  | ok result =>
    simp only [admitted, Except.mapError, Except.ok.injEq] at opened
    subst checked
    exact Int32ByteArrayGroup.File.openFile_snapshot admitted

theorem readAll_rowLimit
    {projection : Int32ByteArrayGroup.DeltaLength.Checked int32Name byteArrayName}
    (opened : Int32ByteArrayGroup.openFile limits.group.group input ⟨int32Name, .required⟩
      ⟨byteArrayName, .optional⟩ = .ok projection)
    (over : limits.maxFileRows < projection.snapshot.metadata.numRows.toNat) :
    Reader.readAll (openSource limits input int32Name byteArrayName) =
      .error (.openFailure (.fileRowLimit limits.maxFileRows projection.snapshot.metadata.numRows.toNat)) := by
  have rejected := Int32ByteArrayGroup.File.openFile_rowLimit (limits := limits.admission) opened over
  unfold openSource openFile
  rw [rejected]
  rfl

theorem readAll_trace (opened : openFile limits input int32Name byteArrayName = .ok checked) :
    let trace := Reader.denoteGroups (source checked).readGroup (List.range checked.projection.snapshot.groupCount)
    Reader.readAll (openSource limits input int32Name byteArrayName) =
      .ok ⟨schema int32Name byteArrayName, ⟨trace.1.map AlignedColumns.ofRows, trace.2⟩⟩ := by
  rw [openSource, opened]
  exact Reader.readAll_opened (source checked)

private theorem denote_append_success (checked : Checked limits int32Name byteArrayName)
    (before after : List Nat) {groups : List (List Int32ByteArrayGroup.Row)}
    (decoded : before.mapM (Int32ByteArrayGroup.DeltaLength.readGroup checked.projection limits.group) =
      .ok groups) :
    let tail := Reader.denoteGroups (source checked).readGroup after
    Reader.denoteGroups (source checked).readGroup (before ++ after) =
      (groups.map (rows int32Name byteArrayName) ++ tail.1, tail.2) := by
  induction before generalizing groups with
  | nil =>
    cases decoded
    rfl
  | cons index rest ih =>
    rw [List.mapM_cons] at decoded
    cases read : Int32ByteArrayGroup.DeltaLength.readGroup checked.projection limits.group index with
    | error reason => simp [read, bind, Except.bind] at decoded
    | ok pairs =>
      simp only [read, bind, Except.bind] at decoded
      cases reads : rest.mapM (Int32ByteArrayGroup.DeltaLength.readGroup checked.projection limits.group) with
      | error reason => simp [reads] at decoded
      | ok following =>
        simp only [reads] at decoded
        cases decoded
        have first : (source checked).readGroup index = .ok (rows int32Name byteArrayName pairs) := by
          simp [source, read, Except.map, Except.mapError]
        simp [Reader.denoteGroups, first, ih reads]

theorem readAll_success {groups : List (List Int32ByteArrayGroup.Row)}
    (opened : openFile limits input int32Name byteArrayName = .ok checked)
    (decoded : (List.range checked.projection.snapshot.groupCount).mapM
      (Int32ByteArrayGroup.DeltaLength.readGroup checked.projection limits.group) = .ok groups) :
    Reader.readAll (openSource limits input int32Name byteArrayName) = .ok ⟨schema int32Name byteArrayName,
      ⟨groups.map (AlignedColumns.ofRows ∘ rows int32Name byteArrayName), .eos⟩⟩ := by
  have ordered := denote_append_success checked (List.range checked.projection.snapshot.groupCount) [] decoded
  simp only [List.append_nil, Reader.denoteGroups] at ordered
  have traceOrder : Reader.denoteGroups (source checked).readGroup
      (List.range checked.projection.snapshot.groupCount) = (groups.map (rows int32Name byteArrayName), .eos) :=
    ordered
  rw [readAll_trace opened, traceOrder]
  simp only [List.map_map]

theorem readAll_first_error {before after : List Nat} {index : Nat}
    {groups : List (List Int32ByteArrayGroup.Row)} {reason : Int32ByteArrayGroup.DeltaLength.Error}
    (opened : openFile limits input int32Name byteArrayName = .ok checked)
    (split : List.range checked.projection.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (Int32ByteArrayGroup.DeltaLength.readGroup checked.projection limits.group) = .ok groups)
    (failed : Int32ByteArrayGroup.DeltaLength.readGroup checked.projection limits.group index = .error reason) :
    Reader.readAll (openSource limits input int32Name byteArrayName) = .ok ⟨schema int32Name byteArrayName,
      ⟨groups.map (AlignedColumns.ofRows ∘ rows int32Name byteArrayName), .readError (.groupFailure index reason)⟩⟩ := by
  have ordered := denote_append_success checked before (index :: after) earlier
  rw [← split] at ordered
  rw [readAll_trace opened, ordered]
  simp [Reader.denoteGroups, source, failed, Except.map, Except.mapError, List.map_map]

private theorem denote_rows_le (checked : Checked limits int32Name byteArrayName) (indices : List Nat) :
    ((Reader.denoteGroups (source checked).readGroup indices).1.map List.length).sum ≤
      (indices.map fun index => ((checked.projection.snapshot.groupAt index).map (·.numRows.toNat)).getD 0).sum := by
  induction indices with
  | nil => simp [Reader.denoteGroups]
  | cons index rest ih =>
    cases read : Int32ByteArrayGroup.DeltaLength.readGroup checked.projection limits.group index with
    | error reason =>
      have failed : (source checked).readGroup index = .error (.groupFailure index reason) := by
        simp [source, read, Except.map, Except.mapError]
      simp [Reader.denoteGroups, failed]
    | ok pairs =>
      have success : (source checked).readGroup index = .ok (rows int32Name byteArrayName pairs) := by
        simp [source, read, Except.map, Except.mapError]
      obtain ⟨group, _, _, intsWire, _, _, _, _, count, _, _⟩ :=
        Int32ByteArrayGroup.DeltaLength.readGroup_wire read
      obtain ⟨_, _, _, _, picked, _⟩ := intsWire
      have size : (rows int32Name byteArrayName pairs).length = group.numRows.toNat := by
        have batch := (Int32ByteArrayGroup.File.batch_projections
          ⟨int32Name, .required⟩ ⟨byteArrayName, .optional⟩ pairs).1
        exact batch.trans count
      simp only [Reader.denoteGroups, success, List.map_cons, List.sum_cons, picked,
        Option.map_some, Option.getD_some, size]
      exact Nat.add_le_add_left ih _

theorem readAll_rows_le
    {selected : Scan.Schema String Kind} {trace : Events.Trace selected Value Error}
    (observed : Reader.readAll (openSource limits input int32Name byteArrayName) = .ok ⟨selected, trace⟩) :
    (trace.batches.map (·.rowCount)).sum ≤ limits.maxFileRows := by
  cases opened : openFile limits input int32Name byteArrayName with
  | error reason => simp [openSource, opened, Except.map, Reader.readAll] at observed
  | ok checked =>
    have cap := denote_rows_le checked (List.range checked.projection.snapshot.groupCount)
    have snapshot := openFile_snapshot opened
    rw [← Snapshot.check_rowCounts snapshot.1] at cap
    rw [readAll_trace opened] at observed
    cases observed
    simpa only [List.map_map, Function.comp_def, AlignedColumns.ofRows] using Nat.le_trans cap snapshot.2

end Silmaril.Proofs.Formats.Parquet.Int32ByteArrayGroup.DeltaLength.File
