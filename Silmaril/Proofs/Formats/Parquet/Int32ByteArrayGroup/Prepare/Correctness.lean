module

public import Silmaril.Formats.Parquet.Int32ByteArrayGroup.Prepare.Defs
import Silmaril.Formats.Parquet.Int32ByteArrayGroup.File.Thms
import Silmaril.Formats.Arrow.Writer.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Int32ByteArrayGroup.Prepare

open Silmaril.Formats
open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Int32ByteArrayGroup
open Silmaril.Formats.Parquet.Int32ByteArrayGroup.Prepare
open Silmaril.Relational

variable {limits : File.Limits} {input : Bytes} {int32 byteArray : Field}
variable {checked : File.Checked limits int32 byteArray}

private theorem read_order (checked : File.Checked limits int32 byteArray) (indices : List Nat) :
    (indices.mapM checked.source.readGroup).toOption =
      (indices.mapM (checked.projection.readGroup limits.group)).toOption.map
        (List.map (File.rows int32 byteArray)) := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
    cases first : checked.projection.readGroup limits.group index with
    | error reason =>
      simp [List.mapM_cons, File.Checked.source, first, Except.map, Except.mapError, Bind.bind, Except.bind,
        Except.toOption]
    | ok pairs =>
      have head : checked.source.readGroup index = .ok (File.rows int32 byteArray pairs) := by
        simp [File.Checked.source, first, Except.map, Except.mapError]
      cases original : rest.mapM (checked.projection.readGroup limits.group) <;>
        cases typed : rest.mapM checked.source.readGroup <;>
          simp_all [List.mapM_cons, Except.toOption, Bind.bind, Except.bind, pure, Except.pure]

private theorem read_length {groups : List (Reader.RowGroup (File.schema int32 byteArray) File.Value)}
    {indices : List Nat} (read : indices.mapM checked.source.readGroup = .ok groups) :
    groups.length = indices.length := by
  induction indices generalizing groups with
  | nil => cases read; rfl
  | cons index rest ih =>
    cases head : checked.source.readGroup index with
    | error cause => simp [List.mapM_cons, head, Bind.bind, Except.bind] at read
    | ok rows =>
      cases later : rest.mapM checked.source.readGroup with
      | error cause => simp [List.mapM_cons, head, later, Bind.bind, Except.bind] at read
      | ok tail =>
        simp [List.mapM_cons, head, later, Bind.bind, Except.bind, pure, Except.pure] at read
        simp [← read, ih later]

theorem batch_values (int32 byteArray : Field) (pairs : List Row) :
    let batch := Batch.ofRows int32 byteArray (File.rows int32 byteArray pairs)
    batch.rowCount = pairs.length ∧ batch.intValues = pairs.map Prod.fst ∧
      batch.viewValues.map (Option.map KBytes.toList) =
        pairs.map (fun pair => pair.2.map Bytes.toList) := by
  obtain ⟨count, integers, binary⟩ := File.batch_projections int32 byteArray pairs
  refine ⟨count, integers, ?_⟩
  change (((AlignedColumns.ofRows (File.rows int32 byteArray pairs)).values
      ⟨1, by change 1 < 2; decide⟩).map
        (Option.map fun bytes => Arrow.Writer.emitWords 1 (bytes.toList.map UInt8.toNat))).map
      (Option.map KBytes.toList) = pairs.map (fun pair => pair.2.map Bytes.toList)
  rw [binary]
  change (List.map (Option.map KBytes.toList)
      ((pairs.map Prod.snd).map (Option.map fun bytes : Bytes =>
        Arrow.Writer.emitWords 1 (bytes.toList.map UInt8.toNat)))) = _
  simp [List.map_map, Option.map_map, Function.comp_def, Arrow.Writer.emitBytes_bytes]

theorem prepare_ok_iff {result : Prepared} :
    prepare limits input int32 byteArray = .ok result ↔
      ∃ checked : File.Checked limits int32 byteArray, File.openFile limits input int32 byteArray = .ok checked ∧
        ∃ groups, (List.range checked.projection.snapshot.groupCount).mapM
          (checked.projection.readGroup limits.group) = .ok groups ∧
          result = ⟨Schema.ofSelection int32 byteArray,
            groups.map (Batch.ofRows int32 byteArray ∘ File.rows int32 byteArray)⟩ := by
  cases opened : File.openFile limits input int32 byteArray with
  | error cause => simp [prepare, opened, Bind.bind, Except.bind]
  | ok checked =>
    have order := read_order checked (List.range checked.projection.snapshot.groupCount)
    change (checked.source.groups.mapM checked.source.readGroup).toOption = _ at order
    cases typed : checked.source.groups.mapM checked.source.readGroup with
    | error cause =>
      cases raw : (List.range checked.projection.snapshot.groupCount).mapM
          (checked.projection.readGroup limits.group) with
      | error reason => simp [prepare, prepareChecked, opened, typed, raw, Bind.bind, Except.bind]
      | ok groups => simp [typed, raw, Except.toOption] at order
    | ok rows =>
      cases raw : (List.range checked.projection.snapshot.groupCount).mapM
          (checked.projection.readGroup limits.group) with
      | error reason => simp [typed, raw, Except.toOption] at order
      | ok groups =>
        have sameRows : rows = groups.map (File.rows int32 byteArray) := by
          simpa [typed, raw, Except.toOption] using order
        simp [prepare, prepareChecked, opened, typed, raw, sameRows, Bind.bind, Except.bind, pure, Except.pure,
          List.map_map, eq_comm]

theorem prepare_group_count {result : Prepared}
    (success : prepare limits input int32 byteArray = .ok result)
    (opened : File.openFile limits input int32 byteArray = .ok checked) :
    result.batches.length = checked.projection.snapshot.groupCount := by
  cases read : checked.source.groups.mapM checked.source.readGroup with
  | error cause => simp [prepare, prepareChecked, opened, read, Bind.bind, Except.bind] at success
  | ok rows =>
    have count := read_length read
    simp [prepare, prepareChecked, opened, read, Bind.bind, Except.bind, pure, Except.pure] at success
    subst result
    simpa [File.Checked.source] using count

theorem prepare_exact {result : Prepared} (success : prepare limits input int32 byteArray = .ok result) :
    ∃ (checked : File.Checked limits int32 byteArray) (groups : List (List Row)),
      File.openFile limits input int32 byteArray = .ok checked ∧
      (List.range checked.projection.snapshot.groupCount).mapM
        (checked.projection.readGroup limits.group) = .ok groups ∧
      result.schema.fields = [⟨int32.name, decide (int32.layout = .optional), .primitive .int32⟩,
        ⟨byteArray.name, decide (byteArray.layout = .optional), .view .binary⟩] ∧
      result.batches.length = checked.projection.snapshot.groupCount ∧
      List.Forall₂ (fun (batch : Batch) pairs => batch.rowCount = pairs.length ∧
        batch.intValues = pairs.map Prod.fst ∧ batch.viewValues.map (Option.map KBytes.toList) =
          pairs.map (fun pair => pair.2.map Bytes.toList)) result.batches groups := by
  obtain ⟨checked, opened, groups, decoded, formed⟩ := prepare_ok_iff.mp success
  refine ⟨checked, groups, opened, decoded, ?_, prepare_group_count success opened, ?_⟩
  · rw [formed]
    rfl
  · rw [formed]
    suffices ∀ rows : List (List Row), List.Forall₂ (fun (batch : Batch) pairs =>
        batch.rowCount = pairs.length ∧ batch.intValues = pairs.map Prod.fst ∧
          batch.viewValues.map (Option.map KBytes.toList) = pairs.map (fun pair => pair.2.map Bytes.toList))
        (rows.map (Batch.ofRows int32 byteArray ∘ File.rows int32 byteArray)) rows from this groups
    intro rows
    induction rows with
    | nil => exact .nil
    | cons pairs later ih => exact .cons (batch_values int32 byteArray pairs) ih

theorem prepare_first_error {before after : List Nat} {index : Nat} {groups : List (List Row)}
    {reason : Int32ByteArrayGroup.Error}
    (opened : File.openFile limits input int32 byteArray = .ok checked)
    (split : List.range checked.projection.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (checked.projection.readGroup limits.group) = .ok groups)
    (failed : checked.projection.readGroup limits.group index = .error reason) :
    prepare limits input int32 byteArray = .error (.groupFailure index reason) ∧
      Reader.readAll (File.openSource limits input int32 byteArray) = .ok
        ⟨File.schema int32 byteArray,
          ⟨groups.map (AlignedColumns.ofRows ∘ File.rows int32 byteArray), .readError (.groupFailure index reason)⟩⟩ := by
  refine ⟨?_, File.readAll_first_error opened split earlier failed⟩
  have earlierTyped : before.mapM checked.source.readGroup = .ok (groups.map (File.rows int32 byteArray)) := by
    have ordered := read_order checked before
    cases decoded : before.mapM checked.source.readGroup <;>
      simp_all [Except.toOption]
  have indexed : checked.source.readGroup index = .error (.groupFailure index reason) := by
    simp [File.Checked.source, failed, Except.map, Except.mapError]
  have indices : checked.source.groups = before ++ index :: after := split
  simp [prepare, prepareChecked, opened, indices, List.mapM_append, earlierTyped, indexed, Bind.bind, Except.bind]

end Silmaril.Proofs.Formats.Parquet.Int32ByteArrayGroup.Prepare
