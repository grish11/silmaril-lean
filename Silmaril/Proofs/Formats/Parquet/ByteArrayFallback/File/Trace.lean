module

public import Silmaril.Formats.Parquet.ByteArrayFallback.File.Defs
import Silmaril.Formats.Parquet.Reader.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.ByteArrayFallback.File

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Arrow Silmaril.Relational
open Silmaril.Formats.Parquet.ByteArrayFallback.File

variable {name : String} {checked : ByteArrayFallback.Checked name}
variable {profile : ByteArrayFallback.Profile}
variable {limits : ByteArrayFallback.Limits} {input : Bytes}

theorem batch_slots (name : String) (slots : List (Option Bytes)) (field : Fin (schema name).width) :
    let batch := AlignedColumns.ofRows (Plain.ByteArray.File.rows name .optional slots)
    batch.rowCount = slots.length ∧ batch.values field = slots := by
  simp [AlignedColumns.ofRows, Plain.ByteArray.File.rows, List.map_map, Function.comp_def]

theorem readAll_orderFor (opened : ByteArrayFallback.openFile limits input name = .ok checked) :
    let trace := Reader.denoteGroups (rowsAtFor profile checked limits) (List.range checked.snapshot.groupCount)
    readAllFor profile limits input name = .ok ⟨schema name, ⟨trace.1.map AlignedColumns.ofRows, trace.2⟩⟩ := by
  rw [readAllFor, openSourceFor, opened]
  exact Reader.readAll_opened (sourceFor profile checked limits)

private theorem denote_successful_prefix {before after : List Nat} {groups : List (List (Option Bytes))}
    (earlier : List.Forall₂ (fun index slots => ByteArrayFallback.readGroupFor profile checked limits index = .ok slots)
      before groups) :
    let tail := Reader.denoteGroups (rowsAtFor profile checked limits) after
    Reader.denoteGroups (rowsAtFor profile checked limits) (before ++ after) =
      (groups.map (Plain.ByteArray.File.rows name .optional) ++ tail.1, tail.2) := by
  induction earlier with
  | nil => rfl
  | cons decoded _ ih =>
    simp [Reader.denoteGroups, rowsAtFor, decoded, Except.map, Except.mapError, ih]

theorem readAll_successFor {groups : List (List (Option Bytes))}
    (opened : ByteArrayFallback.openFile limits input name = .ok checked)
    (decoded : List.Forall₂ (fun index slots => ByteArrayFallback.readGroupFor profile checked limits index = .ok slots)
      (List.range checked.snapshot.groupCount) groups) :
    readAllFor profile limits input name = .ok ⟨schema name,
      ⟨groups.map (AlignedColumns.ofRows ∘ Plain.ByteArray.File.rows name .optional), .eos⟩⟩ := by
  have ordered := denote_successful_prefix (after := []) decoded
  simp only [List.append_nil, Reader.denoteGroups] at ordered
  rw [readAll_orderFor opened, ordered]
  simp only [List.map_map]

theorem readAll_first_errorFor {before after : List Nat} {index : Nat}
    {groups : List (List (Option Bytes))} {cause : ByteArrayFallback.Error}
    (opened : ByteArrayFallback.openFile limits input name = .ok checked)
    (split : List.range checked.snapshot.groupCount = before ++ index :: after)
    (earlier : List.Forall₂ (fun i slots => ByteArrayFallback.readGroupFor profile checked limits i = .ok slots) before groups)
    (failed : ByteArrayFallback.readGroupFor profile checked limits index = .error cause) :
    readAllFor profile limits input name = .ok ⟨schema name,
      ⟨groups.map (AlignedColumns.ofRows ∘ Plain.ByteArray.File.rows name .optional),
        .readError (.readFailure cause)⟩⟩ := by
  rw [readAll_orderFor opened, split, denote_successful_prefix (after := index :: after) earlier]
  simp [Reader.denoteGroups, rowsAtFor, failed, Except.map, Except.mapError, List.map_map]

end Silmaril.Proofs.Formats.Parquet.ByteArrayFallback.File
