module

public import Silmaril.Formats.Parquet.Plain.ByteArray.ToIpc.Source.Defs
import Silmaril.Formats.Arrow.Writer.Thms
import Silmaril.Formats.Relational.BinaryObservation.ParquetFile.Thms
import Silmaril.Formats.Relational.BinaryObservation.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Plain.ByteArray.ToIpc

open Silmaril.Formats
open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Plain.ByteArray
open Silmaril.Formats.Parquet.Plain.ByteArray.ToIpc
open Silmaril.Formats.Arrow.BinaryView
open Silmaril.Relational
open Silmaril.Formats.Relational.BinaryObservation

theorem readSource_ok_iff {limits : File.Limits} {input : Bytes} {name : String}
    {layout : FlatColumn.Layout} {source : Source} :
    readSource limits input name layout = .ok source ↔
      ∃ checked : File.Checked name layout, File.openFile limits input name layout = .ok checked ∧
        (List.range checked.snapshot.groupCount).mapM (checked.readGroup limits) = .ok source.groups ∧
        source.field = ⟨name, decide (layout = .optional)⟩ := by
  cases opened : File.openFile limits input name layout with
  | error error =>
    simp [readSource, opened, Except.mapError, Bind.bind, Except.bind]
  | ok checked =>
    cases decoded : (List.range checked.snapshot.groupCount).mapM (checked.readGroup limits) with
    | error error =>
      simp [readSource, opened, decoded, Except.mapError, Bind.bind, Except.bind]
    | ok groups =>
      rcases source with ⟨field, slots⟩
      simp [readSource, opened, decoded, Except.mapError, Bind.bind, Except.bind, pure, Except.pure,
        Source.mk.injEq, eq_comm, and_comm]

private theorem mapM_length {α β ε : Type} {read : α → Except ε β}
    {indices : List α} {groups : List β} (success : indices.mapM read = .ok groups) :
    groups.length = indices.length := by
  induction indices generalizing groups with
  | nil => cases success; rfl
  | cons first later ih =>
    cases head : read first with
    | error cause => simp [List.mapM_cons, head, Bind.bind, Except.bind] at success
    | ok value =>
      cases tail : later.mapM read with
      | error cause => simp [List.mapM_cons, head, tail, Bind.bind, Except.bind] at success
      | ok rest =>
        simp [List.mapM_cons, head, tail, Bind.bind, Except.bind, pure, Except.pure] at success
        simp [← success, ih tail]

theorem readSource_eos {limits : File.Limits} {input : Bytes} {name : String}
    {layout : FlatColumn.Layout} {source : Source} (success : readSource limits input name layout = .ok source) :
    ∃ checked : File.Checked name layout, File.openFile limits input name layout = .ok checked ∧
      source.batches.length = checked.snapshot.groupCount ∧
      File.readAll limits input name layout = .ok
        ⟨File.schema name layout,
          ⟨source.groups.map (AlignedColumns.ofRows ∘ File.rows name layout), .eos⟩⟩ := by
  obtain ⟨checked, opened, decoded, _⟩ := readSource_ok_iff.mp success
  exact ⟨checked, opened, by simpa [Source.batches] using mapM_length decoded,
    ParquetFile.readAll_success opened decoded⟩

theorem readSource_first_error {limits : File.Limits} {input : Bytes} {name : String}
    {layout : FlatColumn.Layout} {checked : File.Checked name layout} {before after : List Nat} {index : Nat}
    {groups : List (List (Option Bytes))} {cause : FlatColumn.Error File.PageError}
    (opened : File.openFile limits input name layout = .ok checked)
    (indices : List.range checked.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (checked.readGroup limits) = .ok groups)
    (failed : checked.readGroup limits index = .error cause) :
    readSource limits input name layout = .error (.readError cause) ∧
      File.readAll limits input name layout = .ok
        ⟨File.schema name layout,
          ⟨groups.map (AlignedColumns.ofRows ∘ File.rows name layout), .readError (.column cause)⟩⟩ := by
  refine ⟨?_, ParquetFile.readAll_first_error opened indices earlier failed⟩
  simp [readSource, opened, indices, List.mapM_append, earlier, failed, Except.mapError, Bind.bind, Except.bind]

theorem packValue_octets (value : Bytes) : (packValue value).toList = value.toList :=
  Arrow.Writer.emitBytes_bytes value.toList

theorem batches_octets (source : Source) :
    source.batches.map (List.map (Option.map KBytes.toList)) =
      source.groups.map (List.map (Option.map Bytes.toList)) := by
  simp [Source.batches, List.map_map, Option.map_map, Function.comp_def, packValue_octets]

theorem ipcSlots_batches (source : Source) :
    ipcSlots source.batches = source.groups.flatten.map (Option.map Bytes.toList) := by
  rw [ipcSlots, List.map_flatten, batches_octets, ← List.map_flatten]

theorem observeIpc_of_read (source : Source) {ipc : Arrow.Limits} {limits : Column.Limits}
    {wire : KBytes} {batches : List (List (Option KBytes))}
    (decoded : Stream.read ipc limits wire = .ok ⟨source.ipcField, batches⟩)
    (octets : batches.map (List.map (Option.map KBytes.toList)) =
      source.batches.map (List.map (Option.map KBytes.toList))) :
    observeIpc source.field ipc limits wire = .ok
      (observation source.field (source.groups.flatten.map (Option.map Bytes.toList))) := by
  refine observeIpc_ok_iff.mpr ⟨batches, decoded, ?_⟩
  have sameSlots : ipcSlots batches = ipcSlots source.batches := by
    simp only [ipcSlots, List.map_flatten, octets]
  rw [sameSlots, ipcSlots_batches]

end Silmaril.Proofs.Formats.Parquet.Plain.ByteArray.ToIpc
