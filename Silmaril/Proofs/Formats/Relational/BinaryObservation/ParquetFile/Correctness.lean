module

public import Silmaril.Formats.Parquet.Plain.ByteArray.File.Thms
public import Silmaril.Formats.Relational.BinaryObservation.Thms

public section

namespace Silmaril.Proofs.Formats.Relational.BinaryObservation.ParquetFile

open Silmaril.Formats
open Silmaril.Formats.Arrow.BinaryView
open Silmaril.Formats.Relational.BinaryObservation
open Silmaril.Relational

open Silmaril.Formats.Parquet
open Parquet.Plain.ByteArray.File (Checked Limits openFile readAll readAll_order rows schema)

private theorem denoteGroups_prefix {name : String} {layout : FlatColumn.Layout}
    (checked : Checked name layout) (limits : Limits)
    (before after : List Nat) (groups : List (List (Option Bytes)))
    (earlier : before.mapM (checked.readGroup limits) = .ok groups) :
    Reader.denoteGroups (checked.source limits).readGroup (before ++ after) =
      (groups.map (rows name layout) ++
        (Reader.denoteGroups (checked.source limits).readGroup after).1,
        (Reader.denoteGroups (checked.source limits).readGroup after).2) := by
  induction before generalizing groups with
  | nil =>
    cases earlier
    rfl
  | cons index before ih =>
    cases head : checked.readGroup limits index with
    | error cause =>
      simp [List.mapM_cons, head, Bind.bind, Except.bind] at earlier
    | ok slots =>
      cases tail : before.mapM (checked.readGroup limits) with
      | error cause =>
        simp [List.mapM_cons, head, tail, Bind.bind, Except.bind] at earlier
      | ok rest =>
        simp [List.mapM_cons, head, tail, Bind.bind, Except.bind, pure, Except.pure] at earlier
        subst groups
        have step : (checked.source limits).readGroup index = .ok (rows name layout slots) := by
          simp [Checked.source, head, Except.map, Except.mapError]
        simp [Reader.denoteGroups, step, ih rest tail]

theorem readAll_success {limits : Limits} {input : Bytes} {name : String}
    {layout : FlatColumn.Layout} {checked : Checked name layout} {groups : List (List (Option Bytes))}
    (opened : openFile limits input name layout = .ok checked)
    (decoded : (List.range checked.snapshot.groupCount).mapM (checked.readGroup limits) = .ok groups) :
    readAll limits input name layout = .ok
      ⟨schema name layout, ⟨groups.map (AlignedColumns.ofRows ∘ rows name layout), .eos⟩⟩ := by
  have ordered := denoteGroups_prefix checked limits (List.range checked.snapshot.groupCount) [] groups decoded
  simp [Reader.denoteGroups] at ordered
  simpa [ordered, List.map_map] using readAll_order opened

theorem readAll_first_error {limits : Limits} {input : Bytes} {name : String}
    {layout : FlatColumn.Layout} {checked : Checked name layout} {before after : List Nat} {index : Nat}
    {groups : List (List (Option Bytes))} {cause : FlatColumn.Error Plain.ByteArray.File.PageError}
    (opened : openFile limits input name layout = .ok checked)
    (indices : List.range checked.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (checked.readGroup limits) = .ok groups)
    (failed : checked.readGroup limits index = .error cause) :
    readAll limits input name layout = .ok
      ⟨schema name layout, ⟨groups.map (AlignedColumns.ofRows ∘ rows name layout), .readError (.column cause)⟩⟩ := by
  have step : (checked.source limits).readGroup index = .error (.column cause) := by
    simp [Checked.source, failed, Except.map, Except.mapError]
  simpa [indices, denoteGroups_prefix checked limits before (index :: after) groups earlier,
    Reader.denoteGroups, step, List.map_map] using readAll_order opened

theorem common_observation_iff {limits : Limits} {input : Bytes} {name : String}
    {layout : FlatColumn.Layout} {checked : Checked name layout} {groups : List (List (Option Bytes))}
    {ipcField : Field} {ipc : Arrow.Limits} {viewLimits : Column.Limits} {wire : KBytes}
    {batches : List (List (Option KBytes))}
    (opened : openFile limits input name layout = .ok checked)
    (decoded : (List.range checked.snapshot.groupCount).mapM (checked.readGroup limits) = .ok groups)
    (ipcRead : Stream.read ipc viewLimits wire =
      .ok ⟨⟨ipcField.name, ipcField.nullable, .binary⟩, batches⟩) :
    (readAll limits input name layout = .ok
        ⟨schema name layout, ⟨groups.map (AlignedColumns.ofRows ∘ rows name layout), .eos⟩⟩ ∧
      observeIpc ipcField ipc viewLimits wire =
        .ok (observation ⟨name, decide (layout = .optional)⟩ (groups.flatten.map (Option.map Bytes.toList)))) ↔
      (⟨name, decide (layout = .optional)⟩ : Field) = ipcField ∧
        groups.flatten.map (Option.map Bytes.toList) = ipcSlots batches := by
  have observed : observeIpc ipcField ipc viewLimits wire =
      .ok (observation ipcField (ipcSlots batches)) :=
    observeIpc_ok_iff.mpr ⟨batches, ipcRead, rfl⟩
  rw [readAll_success opened decoded, observed]
  simp only [Except.ok.injEq, eq_self, true_and]
  rw [eq_comm]
  exact observation_eq_iff

end Silmaril.Proofs.Formats.Relational.BinaryObservation.ParquetFile
