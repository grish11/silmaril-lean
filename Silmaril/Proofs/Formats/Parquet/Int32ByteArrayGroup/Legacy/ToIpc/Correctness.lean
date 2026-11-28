module

public import Silmaril.Formats.Parquet.Int32ByteArrayGroup.Legacy.ToIpc.Defs
import Batteries.Data.List.Lemmas
import Silmaril.Formats.Arrow.MixedFlat.Stream.Thms
import Silmaril.Formats.Arrow.MixedFlat.StreamWriter.Thms
import Silmaril.Formats.Parquet.Int32ByteArrayGroup.Legacy.Thms
import Silmaril.Formats.Parquet.Int32ByteArrayGroup.ToIpc.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Int32ByteArrayGroup.Legacy.ToIpc

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Arrow
open Silmaril.Formats.Arrow.MixedFlat Silmaril.Relational
open Silmaril.Formats.Parquet.Int32ByteArrayGroup.Legacy.ToIpc

variable {parquet : Int32ByteArrayGroup.Legacy.Limits} {ipc : Arrow.MixedFlat.Limits} {input : Bytes}
variable {int32Name byteArrayName : String} {wire : KBytes}
variable {checked : Int32ByteArrayGroup.Legacy.Checked parquet int32Name byteArrayName}

private theorem indexed_rows (indices : List Nat) :
    indices.mapM (Int32ByteArrayGroup.Legacy.source checked).readGroup =
      (indices.mapM (Int32ByteArrayGroup.Legacy.readGroup checked)).map
        (List.map (Int32ByteArrayGroup.Legacy.rows int32Name byteArrayName)) := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
    rw [List.mapM_cons, List.mapM_cons, ih]
    cases head : Int32ByteArrayGroup.Legacy.readGroup checked index <;>
      cases rest.mapM (Int32ByteArrayGroup.Legacy.readGroup checked) <;>
      simp [Int32ByteArrayGroup.Legacy.source, Int32ByteArrayGroup.Legacy.rowsAt, head, Except.map,
        Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem convert_readback (written : convert parquet ipc input int32Name byteArrayName = .ok wire) :
    ∃ (checked : Int32ByteArrayGroup.Legacy.Checked parquet int32Name byteArrayName)
      (groups : List (List Int32ByteArrayGroup.Row)) (decoded : Stream.Observed),
      Int32ByteArrayGroup.Legacy.openFile parquet input int32Name byteArrayName = .ok checked ∧
      List.Forall₂ (fun index pairs => Int32ByteArrayGroup.Legacy.readGroup checked index = .ok pairs)
        (List.range checked.projection.snapshot.groupCount) groups ∧
      Int32ByteArrayGroup.Legacy.readAll parquet input int32Name byteArrayName =
        .ok ⟨Int32ByteArrayGroup.Legacy.schema int32Name byteArrayName,
          ⟨groups.map (AlignedColumns.ofRows ∘ Int32ByteArrayGroup.Legacy.rows int32Name byteArrayName), .eos⟩⟩ ∧
      Stream.read ipc wire = .ok decoded ∧
      decoded.fields = [⟨int32Name, false, .primitive .int32⟩, ⟨byteArrayName, true, .view .binary⟩] ∧
      decoded.batches.map StreamWriter.observeBatch =
        groups.map (Int32ByteArrayGroup.ToIpc.groupObservation ⟨int32Name, .required⟩ ⟨byteArrayName, .optional⟩) ∧
      wire.wf = true ∧ ∃ start,
        Stream.readSchemaFrame ipc.observation.ipc wire = .ok (decoded.fields, start) ∧
        Stream.BatchesWire ipc wire decoded.fields ipc.observation.ipc.batches 0 start decoded.batches := by
  cases opened : Int32ByteArrayGroup.Legacy.openFile parquet input int32Name byteArrayName with
  | error reason => simp [convert, opened, Except.mapError, Bind.bind, Except.bind] at written
  | ok checked =>
    simp only [convert, opened, Except.mapError, Bind.bind, Except.bind] at written
    let indices := List.range checked.projection.snapshot.groupCount
    change (((indices.mapM (Int32ByteArrayGroup.Legacy.source checked).readGroup).mapError Error.source) >>=
      (fun batches => (StreamWriter.emit ipc (writerSchema int32Name byteArrayName)
        (batches.map (writerBatch int32Name byteArrayName))).mapError Error.writer)) = .ok wire at written
    rw [indexed_rows] at written
    cases indexed : indices.mapM (Int32ByteArrayGroup.Legacy.readGroup checked) with
    | error cause =>
      simp [indexed, Except.map, Except.mapError, Bind.bind, Except.bind] at written
    | ok groups =>
      simp only [indexed, Except.map, Except.mapError, Bind.bind, Except.bind] at written
      have emitted : StreamWriter.emit ipc (writerSchema int32Name byteArrayName)
          ((groups.map (Int32ByteArrayGroup.Legacy.rows int32Name byteArrayName)).map
            (writerBatch int32Name byteArrayName)) = .ok wire := by
        split at written <;> simp_all
      have reads := List.mapM_eq_ok_iff_forall₂.mp indexed
      obtain ⟨decoded, read, fields, batches⟩ := StreamWriter.emit_readback emitted
      have observed : decoded.batches.map StreamWriter.observeBatch =
          groups.map (Int32ByteArrayGroup.ToIpc.groupObservation ⟨int32Name, .required⟩ ⟨byteArrayName, .optional⟩) := by
        rw [batches]
        simp only [List.map_map, Function.comp_def, writerBatch, writerSchema, Int32ByteArrayGroup.Legacy.rows,
          Int32ByteArrayGroup.ToIpc.writerBatch_ofRows_observe]
      exact ⟨checked, groups, decoded, rfl, reads, Int32ByteArrayGroup.Legacy.readAll_success opened reads,
        read, fields, observed, (Stream.read_iff ipc wire decoded).mp read⟩

theorem convert_first_error {before after : List Nat} {index : Nat}
    {groups : List (List Int32ByteArrayGroup.Row)} {cause : Int32ByteArrayGroup.Legacy.Error}
    (opened : Int32ByteArrayGroup.Legacy.openFile parquet input int32Name byteArrayName = .ok checked)
    (split : List.range checked.projection.snapshot.groupCount = before ++ index :: after)
    (earlier : List.Forall₂ (fun i pairs => Int32ByteArrayGroup.Legacy.readGroup checked i = .ok pairs) before groups)
    (failed : Int32ByteArrayGroup.Legacy.readGroup checked index = .error cause) :
    convert parquet ipc input int32Name byteArrayName = .error (.source cause) := by
  unfold convert
  rw [opened]
  change (((List.range checked.projection.snapshot.groupCount).mapM
    (Int32ByteArrayGroup.Legacy.source checked).readGroup).mapError Error.source >>= _) = _
  rw [indexed_rows, split, List.mapM_append, List.mapM_eq_ok_iff_forall₂.mpr earlier, List.mapM_cons, failed]
  rfl

end Silmaril.Proofs.Formats.Parquet.Int32ByteArrayGroup.Legacy.ToIpc
