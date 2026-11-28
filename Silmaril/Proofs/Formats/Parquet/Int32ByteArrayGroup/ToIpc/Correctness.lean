module

public import Silmaril.Formats.Parquet.Int32ByteArrayGroup.ToIpc.Defs
import Silmaril.Formats.Parquet.Int32ByteArrayGroup.Prepare.Thms
import Silmaril.Formats.Arrow.MixedFlat.StreamWriter.Thms
import Silmaril.Formats.Arrow.MixedFlat.Stream.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Int32ByteArrayGroup.ToIpc

open Silmaril.Formats
open Silmaril.Formats.Arrow.MixedFlat
open Silmaril.Formats.Parquet.Int32ByteArrayGroup
open Silmaril.Formats.Parquet.Int32ByteArrayGroup.ToIpc

variable {parquet : File.Limits} {ipc : Arrow.MixedFlat.Limits} {input : Bytes}
variable {int32 byteArray : Parquet.Int32ByteArrayGroup.Field} {wire : KBytes}

theorem convert_ok_iff :
    convert parquet ipc input int32 byteArray = .ok wire ↔
      ∃ prepared, Prepare.prepare parquet input int32 byteArray = .ok prepared ∧
        StreamWriter.emit ipc (writerSchema prepared.schema) (prepared.batches.map writerBatch) = .ok wire := by
  cases source : Prepare.prepare parquet input int32 byteArray with
  | error reason =>
    simp [convert, source, Except.mapError, Bind.bind, Except.bind]
  | ok prepared =>
    cases writer : StreamWriter.emit ipc (writerSchema prepared.schema) (prepared.batches.map writerBatch) <;>
      simp [convert, source, writer, Except.mapError, Bind.bind, Except.bind, eq_comm]

private theorem observe_group {int32 byteArray : Parquet.Int32ByteArrayGroup.Field}
    {batch : Prepare.Batch} {group : List Row} {order : Writer.Order}
    (count : batch.rowCount = group.length) (integers : batch.intValues = group.map Prod.fst)
    (octets : batch.viewValues.map (Option.map KBytes.toList) = group.map (fun pair => pair.2.map Bytes.toList)) :
    (writerBatch batch).observe (writerSchemaOrdered order (Prepare.Schema.ofSelection int32 byteArray)) =
      groupObservationOrdered order int32 byteArray group := by
  simp [writerBatch, writerSchemaOrdered, groupObservationOrdered, StreamWriter.BatchInput.observe, StreamWriter.Schema.recordInput,
    Prepare.Schema.ofSelection, Writer.Input.observe, Writer.Input.intField,
    Writer.Input.viewField, Writer.Input.intColumn, Arrow.Writer.ColumnValues.observe,
    count, integers, octets, List.map_map, Function.comp_def]

theorem writerBatch_ofRows_observe (int32 byteArray : Parquet.Int32ByteArrayGroup.Field) (pairs : List Row) :
    (writerBatch (Prepare.Batch.ofRows int32 byteArray (File.rows int32 byteArray pairs))).observe
        (writerSchema (Prepare.Schema.ofSelection int32 byteArray)) =
      groupObservation int32 byteArray pairs := by
  obtain ⟨count, integers, octets⟩ := Prepare.batch_values int32 byteArray pairs
  exact observe_group count integers octets

private theorem readback_of_prepared {order : Writer.Order} {prepared : Prepare.Prepared}
    (finished : Prepare.prepare parquet input int32 byteArray = .ok prepared)
    (emitted : StreamWriter.emit ipc (writerSchemaOrdered order prepared.schema)
      (prepared.batches.map writerBatch) = .ok wire) :
    ∃ (checked : File.Checked parquet int32 byteArray) (groups : List (List Row)) (decoded : Stream.Observed),
      File.openFile parquet input int32 byteArray = .ok checked ∧
      (List.range checked.projection.snapshot.groupCount).mapM
        (checked.projection.readGroup parquet.group) = .ok groups ∧
      Stream.read ipc wire = .ok decoded ∧
      decoded.fields = (writerSchemaOrdered order (Prepare.Schema.ofSelection int32 byteArray)).fields ∧
      decoded.batches.map StreamWriter.observeBatch = groups.map (groupObservationOrdered order int32 byteArray) ∧
      decoded.batches.map (fun batch => batch.observed.rowCount) = groups.map List.length ∧
      decoded.batches.length = checked.projection.snapshot.groupCount ∧
      wire.wf = true ∧ ∃ start,
        Stream.readSchemaFrame ipc.observation.ipc wire = .ok (decoded.fields, start) ∧
        Stream.BatchesWire ipc wire decoded.fields ipc.observation.ipc.batches 0 start decoded.batches := by
  obtain ⟨checked, groups, opened, indexed, _, groupCount, paired⟩ := Prepare.prepare_exact finished
  obtain ⟨decoded, read, writerFields, writerValues⟩ := StreamWriter.emit_readback emitted
  have declaration : prepared.schema = Prepare.Schema.ofSelection int32 byteArray := by
    obtain ⟨_, _, _, _, formed⟩ := Prepare.prepare_ok_iff.mp finished
    exact congrArg Prepare.Prepared.schema formed
  have preservesPairs :
      (prepared.batches.map writerBatch).map
          (StreamWriter.BatchInput.observe (writerSchemaOrdered order (Prepare.Schema.ofSelection int32 byteArray))) =
        groups.map (groupObservationOrdered order int32 byteArray) := by
    suffices ∀ {batches : List Prepare.Batch} {rows : List (List Row)},
        List.Forall₂ (fun (batch : Prepare.Batch) pairs => batch.rowCount = pairs.length ∧
          batch.intValues = pairs.map Prod.fst ∧ batch.viewValues.map (Option.map KBytes.toList) =
            pairs.map (fun pair => pair.2.map Bytes.toList)) batches rows →
        (batches.map writerBatch).map
            (StreamWriter.BatchInput.observe (writerSchemaOrdered order (Prepare.Schema.ofSelection int32 byteArray))) =
          rows.map (groupObservationOrdered order int32 byteArray) from this paired
    intro batches rows relation
    induction relation with
    | nil => rfl
    | cons head later ih =>
      exact congrArg₂ List.cons (observe_group (int32 := int32) (byteArray := byteArray) head.1 head.2.1 head.2.2) ih
  rw [declaration] at writerFields writerValues
  have exactBatches := writerValues.trans preservesPairs
  have sizes : decoded.batches.map (fun batch => batch.observed.rowCount) = groups.map List.length := by
    simpa [List.map_map, Function.comp_def, StreamWriter.observeBatch, groupObservationOrdered]
      using congrArg (List.map Prod.fst) exactBatches
  have count : decoded.batches.length = checked.projection.snapshot.groupCount := by
    have readCount : decoded.batches.length = prepared.batches.length := by
      simpa using congrArg List.length writerValues
    exact readCount.trans groupCount
  exact ⟨checked, groups, decoded, opened, indexed, read, writerFields, exactBatches, sizes, count,
    (Stream.read_iff ipc wire decoded).mp read⟩

theorem convert_readback (written : convert parquet ipc input int32 byteArray = .ok wire) :
    ∃ (checked : File.Checked parquet int32 byteArray) (groups : List (List Row)) (decoded : Stream.Observed),
      File.openFile parquet input int32 byteArray = .ok checked ∧
      (List.range checked.projection.snapshot.groupCount).mapM
        (checked.projection.readGroup parquet.group) = .ok groups ∧
      Stream.read ipc wire = .ok decoded ∧
      decoded.fields = (Prepare.Schema.ofSelection int32 byteArray).fields ∧
      decoded.batches.map StreamWriter.observeBatch = groups.map (groupObservation int32 byteArray) ∧
      decoded.batches.map (fun batch => batch.observed.rowCount) = groups.map List.length ∧
      decoded.batches.length = checked.projection.snapshot.groupCount ∧
      wire.wf = true ∧ ∃ start,
        Stream.readSchemaFrame ipc.observation.ipc wire = .ok (decoded.fields, start) ∧
        Stream.BatchesWire ipc wire decoded.fields ipc.observation.ipc.batches 0 start decoded.batches := by
  obtain ⟨prepared, finished, emitted⟩ := convert_ok_iff.mp written
  exact readback_of_prepared (order := .intFirst) finished emitted

theorem convertOrdered_ok_iff :
    convertOrdered parquet ipc input int32 byteArray = .ok wire ↔
      ∃ (checked : File.Checked parquet int32 byteArray) (prepared : Prepare.Prepared),
        File.openFile parquet input int32 byteArray = .ok checked ∧
        Prepare.prepareChecked checked = .ok prepared ∧
        StreamWriter.emit ipc (writerSchemaOrdered (selectedOrder checked.projection) prepared.schema)
          (prepared.batches.map writerBatch) = .ok wire := by
  cases opened : File.openFile parquet input int32 byteArray with
  | error cause => simp [convertOrdered, opened, Except.mapError, Bind.bind, Except.bind]
  | ok checked =>
    cases source : Prepare.prepareChecked checked with
    | error cause => simp [convertOrdered, opened, source, Except.mapError, Bind.bind, Except.bind]
    | ok prepared =>
      cases writer : StreamWriter.emit ipc (writerSchemaOrdered (selectedOrder checked.projection) prepared.schema)
          (prepared.batches.map writerBatch) <;>
        simp [convertOrdered, opened, source, writer, Except.mapError, Bind.bind, Except.bind, eq_comm]

theorem convertOrdered_readback (written : convertOrdered parquet ipc input int32 byteArray = .ok wire) :
    ∃ (checked : File.Checked parquet int32 byteArray) (groups : List (List Row)) (decoded : Stream.Observed),
      File.openFile parquet input int32 byteArray = .ok checked ∧
      (List.range checked.projection.snapshot.groupCount).mapM
        (checked.projection.readGroup parquet.group) = .ok groups ∧
      Stream.read ipc wire = .ok decoded ∧
      decoded.fields = (writerSchemaOrdered (selectedOrder checked.projection) (Prepare.Schema.ofSelection int32 byteArray)).fields ∧
      decoded.batches.map StreamWriter.observeBatch = groups.map (groupObservationOrdered (selectedOrder checked.projection) int32 byteArray) ∧
      decoded.batches.map (fun batch => batch.observed.rowCount) = groups.map List.length ∧
      decoded.batches.length = checked.projection.snapshot.groupCount ∧
      wire.wf = true ∧ ∃ start,
        Stream.readSchemaFrame ipc.observation.ipc wire = .ok (decoded.fields, start) ∧
        Stream.BatchesWire ipc wire decoded.fields ipc.observation.ipc.batches 0 start decoded.batches := by
  obtain ⟨checked, prepared, opened, source, emitted⟩ := convertOrdered_ok_iff.mp written
  have finished : Prepare.prepare parquet input int32 byteArray = .ok prepared := by
    simp [Prepare.prepare, opened, source, Bind.bind, Except.bind]
  obtain ⟨actual, groups, decoded, actualOpen, rest⟩ := readback_of_prepared finished emitted
  rw [opened] at actualOpen
  cases actualOpen
  exact ⟨checked, groups, decoded, opened, rest⟩

end Silmaril.Proofs.Formats.Parquet.Int32ByteArrayGroup.ToIpc
