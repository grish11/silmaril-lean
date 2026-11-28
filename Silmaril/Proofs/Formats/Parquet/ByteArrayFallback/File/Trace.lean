module

public import Silmaril.Formats.Parquet.ByteArrayFallback.File.Defs
import Silmaril.Formats.Parquet.Reader.Thms
import Silmaril.Semantics.Relational.Table.Thms

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

private theorem scan_batches {selected : Scan.Schema String FlatColumn.Layout}
    (projection : (schema : Scan.Schema String FlatColumn.Layout) → Scan.Projection schema)
    (keep : (schema : Scan.Schema String FlatColumn.Layout) → Scan.Predicate schema Value)
    (groups : List (Reader.RowGroup selected Value)) (termination : Events.Termination ByteArrayFallback.File.Error) :
    (Events.EventStream.scan (.ok ⟨selected, ⟨groups.map AlignedColumns.ofRows, termination⟩⟩)
      projection keep) =
      .ok ⟨(projection selected).schema,
        ⟨groups.map (fun rows => AlignedColumns.ofRows ((projection selected).scan (keep selected) rows)),
          termination⟩⟩ := by
  simp [Events.EventStream.scan, Except.map, Events.Trace.scan, List.map_map, Function.comp_def]

theorem scan_readAllLegacy_order (opened : ByteArrayFallback.openFile limits input name = .ok checked)
    (projection : (schema : Scan.Schema String FlatColumn.Layout) → Scan.Projection schema)
    (keep : (schema : Scan.Schema String FlatColumn.Layout) → Scan.Predicate schema Value) :
    let selected := schema name
    let trace := Reader.denoteGroups (rowsAtFor .plainDictionaryV1 checked limits)
      (List.range checked.snapshot.groupCount)
    ((readAllLegacy limits input name).scan projection keep) = .ok ⟨(projection selected).schema,
      ⟨trace.1.map (fun rows => AlignedColumns.ofRows ((projection selected).scan (keep selected) rows)),
        trace.2⟩⟩ := by
  change ((readAllFor .plainDictionaryV1 limits input name).scan projection keep) = _
  rw [readAll_orderFor opened]
  exact scan_batches projection keep _ _

theorem scan_readAllLegacy_first_error {before after : List Nat} {index : Nat}
    {groups : List (List (Option Bytes))} {cause : ByteArrayFallback.Error}
    (opened : ByteArrayFallback.openFile limits input name = .ok checked)
    (split : List.range checked.snapshot.groupCount = before ++ index :: after)
    (earlier : List.Forall₂ (fun i slots => ByteArrayFallback.readLegacyGroup checked limits i = .ok slots) before groups)
    (failed : ByteArrayFallback.readLegacyGroup checked limits index = .error cause)
    (projection : (schema : Scan.Schema String FlatColumn.Layout) → Scan.Projection schema)
    (keep : (schema : Scan.Schema String FlatColumn.Layout) → Scan.Predicate schema Value) :
    let selected := schema name
    ((readAllLegacy limits input name).scan projection keep) = .ok ⟨(projection selected).schema,
      ⟨groups.map (fun slots => AlignedColumns.ofRows
        ((projection selected).scan (keep selected) (Plain.ByteArray.File.rows name .optional slots))),
        .readError (.readFailure cause)⟩⟩ := by
  change ((readAllFor .plainDictionaryV1 limits input name).scan projection keep) = _
  rw [readAll_first_errorFor opened split earlier failed, ← List.map_map]
  simpa only [List.map_map, Function.comp_def] using
    (scan_batches (selected := schema name) projection keep
      (groups.map (Plain.ByteArray.File.rows name .optional)) (.readError (.readFailure cause)))

end Silmaril.Proofs.Formats.Parquet.ByteArrayFallback.File
