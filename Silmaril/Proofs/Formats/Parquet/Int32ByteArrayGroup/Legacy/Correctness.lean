module

public import Silmaril.Formats.Parquet.Int32ByteArrayGroup.Legacy.Defs
import Silmaril.Formats.Arrow.Events.Thms
import Silmaril.Formats.Parquet.ByteArrayFallback.Thms
import Silmaril.Formats.Parquet.FlatColumn.Thms
import Silmaril.Formats.Parquet.Int32ByteArrayGroup.File.Thms
import Silmaril.Formats.Parquet.Reader.Thms
import Silmaril.Semantics.Relational.Scan.Thms
import Silmaril.Semantics.Relational.Table.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Int32ByteArrayGroup.Legacy

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Arrow Silmaril.Relational
open Silmaril.Formats.Parquet.Int32ByteArrayGroup.Legacy

variable {limits : Limits} {input : Bytes} {int32Name byteArrayName : String}
variable {checked : Checked limits int32Name byteArrayName}

theorem openFile_snapshot (opened : openFile limits input int32Name byteArrayName = .ok checked) :
    Snapshot.check (Failure := Unit) limits.file.group.snapshot input = .ok checked.projection.snapshot ∧
    checked.projection.snapshot.metadata.numRows.toNat ≤ limits.file.maxFileRows := by
  unfold openFile at opened
  cases read : Int32ByteArrayGroup.File.openFile limits.file input
      ⟨int32Name, .required⟩ ⟨byteArrayName, .optional⟩ <;>
    simp [read, Except.mapError] at opened
  cases opened
  exact Int32ByteArrayGroup.File.openFile_snapshot read

theorem readGroup_wire {index : Nat} {pairs : List Int32ByteArrayGroup.Row}
    (read : readGroup checked index = .ok pairs) : GroupWire checked index pairs := by
  cases left : readInts checked index with
  | error cause =>
    simp [readGroup, left, Except.mapError, Bind.bind, Except.bind] at read
  | ok integers =>
    cases right : readBytes checked index with
    | error cause =>
      simp [readGroup, left, right, Except.mapError, Bind.bind, Except.bind] at read
    | ok bytes =>
      obtain ⟨group, intsWire⟩ := FlatColumn.readColumn_wire left
      obtain ⟨other, bytesWire⟩ := ByteArrayFallback.readBoundLegacyGroup_wire right
      have ⟨_, _, _, _, leftAt, _, _, _, _, _, _, _, _, _, _, leftCount⟩ := intsWire
      have ⟨_, _, _, _, rightAt, _, _, _, _, _, _, _, frames⟩ := bytesWire
      have ⟨_, _, _, _, _, _, _, _, _, _, rightCount⟩ := frames
      have same := Option.some.inj (leftAt.symm.trans rightAt)
      subst other
      have equal := leftCount.trans rightCount.symm
      simp [readGroup, left, right, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure, equal] at read
      subst pairs
      exact ⟨group, integers, bytes, intsWire, bytesWire,
        by rw [List.length_zip, leftCount, rightCount, Nat.min_self], rfl, List.unzip_zip equal⟩

theorem readAll_order (opened : openFile limits input int32Name byteArrayName = .ok checked) :
    let trace := Reader.denoteGroups (rowsAt checked) (List.range checked.projection.snapshot.groupCount)
    readAll limits input int32Name byteArrayName = .ok ⟨schema int32Name byteArrayName,
      ⟨trace.1.map AlignedColumns.ofRows, trace.2⟩⟩ := by
  rw [readAll, openSource, opened]
  exact Reader.readAll_opened (source checked)

private theorem denote_prefix {before after : List Nat} {groups : List (List Int32ByteArrayGroup.Row)}
    (earlier : List.Forall₂ (fun index pairs => readGroup checked index = .ok pairs) before groups) :
    let tail := Reader.denoteGroups (rowsAt checked) after
    Reader.denoteGroups (rowsAt checked) (before ++ after) =
      (groups.map (rows int32Name byteArrayName) ++ tail.1, tail.2) := by
  induction earlier with
  | nil => rfl
  | cons read _ ih => simp [Reader.denoteGroups, rowsAt, read, Except.map, ih]

theorem readAll_success {groups : List (List Int32ByteArrayGroup.Row)}
    (opened : openFile limits input int32Name byteArrayName = .ok checked)
    (decoded : List.Forall₂ (fun index pairs => readGroup checked index = .ok pairs)
      (List.range checked.projection.snapshot.groupCount) groups) :
    readAll limits input int32Name byteArrayName = .ok ⟨schema int32Name byteArrayName,
      ⟨groups.map (AlignedColumns.ofRows ∘ rows int32Name byteArrayName), .eos⟩⟩ := by
  have complete := denote_prefix (after := []) decoded
  simp only [List.append_nil, Reader.denoteGroups] at complete
  rw [readAll_order opened, complete]
  simp only [List.map_map]

theorem readAll_first_error {before after : List Nat} {index : Nat}
    {groups : List (List Int32ByteArrayGroup.Row)} {cause : Error}
    (opened : openFile limits input int32Name byteArrayName = .ok checked)
    (split : List.range checked.projection.snapshot.groupCount = before ++ index :: after)
    (earlier : List.Forall₂ (fun i pairs => readGroup checked i = .ok pairs) before groups)
    (failed : readGroup checked index = .error cause) :
    readAll limits input int32Name byteArrayName = .ok ⟨schema int32Name byteArrayName,
      ⟨groups.map (AlignedColumns.ofRows ∘ rows int32Name byteArrayName), .readError cause⟩⟩ := by
  rw [readAll_order opened, split, denote_prefix (after := index :: after) earlier]
  simp [Reader.denoteGroups, rowsAt, failed, Except.map, List.map_map]

section Scan

variable (project : (selected : Scan.Schema String Kind) → Scan.Projection selected)
variable (keep : (selected : Scan.Schema String Kind) → Scan.Predicate selected Value)

private theorem scan_batches {selected : Scan.Schema String Kind}
    (groups : List (Reader.RowGroup selected Value)) (termination : Events.Termination Error) :
    Events.EventStream.scan (.ok ⟨selected, ⟨groups.map AlignedColumns.ofRows, termination⟩⟩) project keep =
      .ok ⟨(project selected).schema,
        ⟨groups.map (fun group => AlignedColumns.ofRows ((project selected).scan (keep selected) group)),
          termination⟩⟩ := by
  simp [Events.EventStream.scan, Except.map, Events.Trace.scan, List.map_map, Function.comp_def]

theorem scan_readAll_order (opened : openFile limits input int32Name byteArrayName = .ok checked) :
    let selected := schema int32Name byteArrayName
    let trace := Reader.denoteGroups (rowsAt checked) (List.range checked.projection.snapshot.groupCount)
    (readAll limits input int32Name byteArrayName).scan project keep = .ok ⟨(project selected).schema,
      ⟨trace.1.map (fun group => AlignedColumns.ofRows ((project selected).scan (keep selected) group)),
        trace.2⟩⟩ := by
  rw [readAll_order opened]
  exact scan_batches project keep _ _

theorem scan_readAll_counts (opened : openFile limits input int32Name byteArrayName = .ok checked) :
    let selected := schema int32Name byteArrayName
    let trace := Reader.denoteGroups (rowsAt checked) (List.range checked.projection.snapshot.groupCount)
    ((readAll limits input int32Name byteArrayName).scan project keep).map
        (fun result => result.2.batches.map (·.rowCount)) =
      .ok (trace.1.map (fun group => (Scan.select (keep selected) group).length)) := by
  rw [scan_readAll_order project keep opened]
  simp [Except.map, List.map_map, Function.comp_def, AlignedColumns.ofRows]

theorem scan_readAll_first_error {before after : List Nat} {index : Nat}
    {groups : List (List Int32ByteArrayGroup.Row)} {cause : Error}
    (opened : openFile limits input int32Name byteArrayName = .ok checked)
    (split : List.range checked.projection.snapshot.groupCount = before ++ index :: after)
    (earlier : List.Forall₂ (fun i pairs => readGroup checked i = .ok pairs) before groups)
    (failed : readGroup checked index = .error cause) :
    let selected := schema int32Name byteArrayName
    (readAll limits input int32Name byteArrayName).scan project keep = .ok ⟨(project selected).schema,
      ⟨groups.map (fun pairs => AlignedColumns.ofRows
        ((project selected).scan (keep selected) (rows int32Name byteArrayName pairs))), .readError cause⟩⟩ := by
  rw [readAll_first_error opened split earlier failed, ← List.map_map]
  simpa only [List.map_map, Function.comp_def] using
    (scan_batches project keep (groups.map (rows int32Name byteArrayName)) (.readError cause))

theorem scan_readAll_equivalent_iff (opened : openFile limits input int32Name byteArrayName = .ok checked)
    (candidate : Events.Trace (project (schema int32Name byteArrayName)).schema Value Error) :
    let selected := schema int32Name byteArrayName
    let trace := Reader.denoteGroups (rowsAt checked) (List.range checked.projection.snapshot.groupCount)
    Events.EventStream.Equivalent ((readAll limits input int32Name byteArrayName).scan project keep)
      (.ok ⟨(project selected).schema, candidate⟩) ↔
      (project selected).scan (keep selected) trace.1.flatten = candidate.rows ∧ trace.2 = candidate.termination := by
  rw [readAll_order opened]
  simp only [Events.EventStream.scan, Except.map]
  rw [Events.EventStream.equivalent_open_iff, Events.Trace.rows_scan, Events.Trace.termination_scan]
  simp [Events.Trace.rows, List.flatMap_map, Function.comp_def, List.flatMap_id']

end Scan

end Silmaril.Proofs.Formats.Parquet.Int32ByteArrayGroup.Legacy
