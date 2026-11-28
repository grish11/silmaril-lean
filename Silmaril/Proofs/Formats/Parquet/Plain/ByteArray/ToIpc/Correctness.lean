module

public import Silmaril.Formats.Parquet.Plain.ByteArray.ToIpc.Defs
import Silmaril.Formats.Parquet.Plain.ByteArray.ToIpc.Source.Thms
import Silmaril.Formats.Arrow.BinaryView.StreamWriter.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Plain.ByteArray.ToIpc

open Silmaril.Formats
open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Plain.ByteArray
open Silmaril.Formats.Parquet.Plain.ByteArray.ToIpc
open Silmaril.Formats.Arrow.BinaryView
open Silmaril.Formats.Relational.BinaryObservation

variable {parquet : File.Limits} {ipc : Arrow.Limits} {view : Column.Limits}
variable {input : Bytes} {name : String} {layout : FlatColumn.Layout} {wire : KBytes}

theorem convert_ok_iff :
    convert parquet ipc view input name layout = .ok wire ↔
      ∃ source, readSource parquet input name layout = .ok source ∧
        StreamWriter.emit ipc view source.ipcField source.batches = .ok wire := by
  cases prepared : readSource parquet input name layout with
  | error cause =>
    simp [convert, prepared, Except.mapError, Bind.bind, Except.bind]
  | ok source =>
    cases emitted : StreamWriter.emit ipc view source.ipcField source.batches <;>
      simp [convert, prepared, emitted, Except.mapError, Bind.bind, Except.bind, eq_comm]

theorem convert_readback (written : convert parquet ipc view input name layout = .ok wire) :
    ∃ (checked : File.Checked name layout) (groups : List (List (Option Bytes)))
      (batches : List (List (Option KBytes))),
      File.openFile parquet input name layout = .ok checked ∧
      (List.range checked.snapshot.groupCount).mapM (checked.readGroup parquet) = .ok groups ∧
      Stream.read ipc view wire = .ok ⟨⟨name, decide (layout = .optional), .binary⟩, batches⟩ ∧
      batches.map (List.map (Option.map KBytes.toList)) =
        groups.map (List.map (Option.map Bytes.toList)) ∧
      batches.map List.length = groups.map List.length ∧ batches.length = checked.snapshot.groupCount ∧
      observeIpc ⟨name, decide (layout = .optional)⟩ ipc view wire =
        .ok (observation ⟨name, decide (layout = .optional)⟩ (groups.flatten.map (Option.map Bytes.toList))) := by
  obtain ⟨source, prepared, emitted⟩ := convert_ok_iff.mp written
  obtain ⟨checked, opened, groupsRead, field⟩ := readSource_ok_iff.mp prepared
  obtain ⟨batches, decoded, sameOctets⟩ := StreamWriter.emit_binary_readback emitted
  have batchOctets := sameOctets.trans (batches_octets source)
  have rowCounts : batches.map List.length = source.groups.map List.length := by
    simpa [List.map_map, Function.comp_def] using congrArg (List.map List.length) batchOctets
  have batchCount : batches.length = checked.snapshot.groupCount := by
    obtain ⟨bound, opened', count, _⟩ := readSource_eos prepared
    have same : checked = bound := Except.ok.inj (opened.symm.trans opened')
    have size : batches.length = source.batches.length := by
      simpa using congrArg List.length sameOctets
    exact size.trans (same ▸ count)
  have observed := observeIpc_of_read source decoded sameOctets
  have fieldRead : Stream.read ipc view wire = .ok ⟨⟨source.field.name, source.field.nullable, .binary⟩, batches⟩ :=
    decoded
  rw [field] at fieldRead
  exact ⟨checked, source.groups, batches, opened, groupsRead,
    fieldRead, batchOctets, rowCounts, batchCount,
    by simpa [field] using observed⟩

end Silmaril.Proofs.Formats.Parquet.Plain.ByteArray.ToIpc
