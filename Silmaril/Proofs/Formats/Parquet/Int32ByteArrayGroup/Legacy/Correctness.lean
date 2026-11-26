module

public import Silmaril.Formats.Parquet.Int32ByteArrayGroup.Legacy.Defs
import Silmaril.Formats.Parquet.ByteArrayFallback.Thms
import Silmaril.Formats.Parquet.FlatColumn.Thms
import Silmaril.Formats.Parquet.Int32ByteArrayGroup.File.Thms
import Silmaril.Formats.Parquet.Reader.Thms

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

end Silmaril.Proofs.Formats.Parquet.Int32ByteArrayGroup.Legacy
