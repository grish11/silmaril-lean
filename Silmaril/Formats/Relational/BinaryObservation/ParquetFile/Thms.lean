module

public import Silmaril.Formats.Parquet.Plain.ByteArray.File.Defs
public import Silmaril.Formats.Relational.BinaryObservation.Defs
import Silmaril.Proofs.Formats.Relational.BinaryObservation.ParquetFile.Correctness

/-! Compare the checked, explicitly selected file projection with a BinaryView
IPC observation of the same ordered nullable octets. -/

public section

namespace Silmaril.Formats.Relational.BinaryObservation.ParquetFile

open Silmaril.Relational
open Silmaril.Formats.Arrow.BinaryView
open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Plain.ByteArray.File (Checked Limits openFile readAll rows schema)

/-- A checked open and all successful indexed reads yield exactly the selected
schema and one batch per footer group, followed by EOS. -/
theorem readAll_success {limits : Limits} {input : Bytes} {name : String}
    {layout : FlatColumn.Layout} {checked : Checked name layout} {groups : List (List (Option Bytes))}
    (opened : openFile limits input name layout = .ok checked)
    (decoded : (List.range checked.snapshot.groupCount).mapM (checked.readGroup limits) = .ok groups) :
    readAll limits input name layout = .ok
      ⟨schema name layout, ⟨groups.map (AlignedColumns.ofRows ∘ rows name layout), .eos⟩⟩ :=
  Proofs.Formats.Relational.BinaryObservation.ParquetFile.readAll_success opened decoded

/-- An open failure returns the original error before any schema or batch. -/
theorem readAll_open_error {limits : Limits} {input : Bytes} {name : String}
    {layout : FlatColumn.Layout} {cause : Plain.ByteArray.File.Error}
    (failed : openFile limits input name layout = .error cause) :
    readAll limits input name layout = .error cause := by
  rw [readAll, failed]
  rfl

/-- Full consumption retains precisely the preceding successful groups and
the original column error, with no batch from the failed or later groups. -/
theorem readAll_first_error {limits : Limits} {input : Bytes} {name : String}
    {layout : FlatColumn.Layout} {checked : Checked name layout} {before after : List Nat} {index : Nat}
    {groups : List (List (Option Bytes))} {cause : FlatColumn.Error Plain.ByteArray.File.PageError}
    (opened : openFile limits input name layout = .ok checked)
    (indices : List.range checked.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (checked.readGroup limits) = .ok groups)
    (failed : checked.readGroup limits index = .error cause) :
    readAll limits input name layout = .ok
      ⟨schema name layout, ⟨groups.map (AlignedColumns.ofRows ∘ rows name layout), .readError (.column cause)⟩⟩ :=
  Proofs.Formats.Relational.BinaryObservation.ParquetFile.readAll_first_error opened indices earlier failed

/-- Successfully exhausted sources agree exactly on the selected name,
nullability, and ordered nullable octets, independent of their boundaries. -/
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
        groups.flatten.map (Option.map Bytes.toList) = ipcSlots batches :=
  Proofs.Formats.Relational.BinaryObservation.ParquetFile.common_observation_iff opened decoded ipcRead

end Silmaril.Formats.Relational.BinaryObservation.ParquetFile
