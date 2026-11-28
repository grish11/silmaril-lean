module

public import Silmaril.Formats.Arrow.MixedFlat.Stream.Defs
import Silmaril.Proofs.Formats.Arrow.MixedFlat.Stream

@[expose] public section

namespace Silmaril.Formats.Arrow.MixedFlat.Stream

/-- The stream field list comes from the initial padded Schema metadata. -/
theorem readSchemaFrame_iff (ipc : Arrow.Limits) (input : KBytes) (fields : List Field) (next : Nat) :
    readSchemaFrame ipc input = .ok (fields, next) ↔
      ∃ size, readEnvelope ipc input 0 = .ok (.metadata size) ∧
        MixedFlat.readSchema ipc (input.slice 8 size) = .ok fields ∧ next = 8 + size :=
  Proofs.Formats.Arrow.MixedFlat.Stream.readSchemaFrame_iff ipc input fields next

/-- A successful record preserves its declared range and the checked batch
observation on that body, within the running stream budget. -/
theorem readRecord_iff (limits : MixedFlat.Limits) (input : KBytes) (fields : List Field)
    (rowsBefore offset size : Nat) (batch : Batch) :
    readRecord limits input fields rowsBefore offset size = .ok batch ↔
      RecordWire limits input fields rowsBefore offset size batch :=
  Proofs.Formats.Arrow.MixedFlat.Stream.readRecord_iff limits input fields rowsBefore offset size batch

/-- The suffix observation has one record per frame in order and ends at
the exact end of the carrier. -/
theorem readBatches_iff (limits : MixedFlat.Limits) (input : KBytes) (fields : List Field)
    (remaining index rowsBefore offset : Nat) (batches : List Batch) :
    readBatches limits input fields remaining index rowsBefore offset = .ok batches ↔
      BatchesWire limits input fields remaining rowsBefore offset batches :=
  Proofs.Formats.Arrow.MixedFlat.Stream.readBatches_iff limits input fields remaining index rowsBefore offset batches

/-- The first checked Schema governs all ordered record frames through EOS. -/
theorem read_iff (limits : MixedFlat.Limits) (input : KBytes) (result : Observed) :
    read limits input = .ok result ↔
      input.wf = true ∧
        ∃ start, readSchemaFrame limits.observation.ipc input = .ok (result.fields, start) ∧
          BatchesWire limits input result.fields limits.observation.ipc.batches 0 start result.batches :=
  Proofs.Formats.Arrow.MixedFlat.Stream.read_iff limits input result

/-- Given an admitted envelope, the returned offsets advance within the
carrier and select the exact original metadata and body bytes. -/
theorem RecordWire.ranges {limits : MixedFlat.Limits} {input : KBytes} {fields : List Field}
    {rowsBefore offset size : Nat} {batch : Batch} (wf : input.wf = true)
    (envelope : readEnvelope limits.observation.ipc input offset = .ok (.metadata size))
    (wire : RecordWire limits input fields rowsBefore offset size batch) :
    batch.range.offset = offset ∧ batch.range.metadataSize = size ∧
    offset < batch.range.next ∧ batch.range.next ≤ input.len ∧
    (batch.range.metadataSlice input).toList = (input.toList.drop (offset + 8)).take size ∧
    (batch.range.bodySlice input).toList =
      (input.toList.drop batch.range.bodyStart).take batch.range.bodyLength :=
  Proofs.Formats.Arrow.MixedFlat.Stream.record_ranges wf envelope wire

/-- Standalone batch decoding on the reported range gives the same
observation when paired with the checked Schema. -/
theorem RecordWire.decode {limits : MixedFlat.Limits} {input schemaBytes : KBytes} {fields : List Field}
    {rowsBefore offset size : Nat} {batch : Batch}
    (schema : MixedFlat.readSchema limits.observation.ipc schemaBytes = .ok fields)
    (wire : RecordWire limits input fields rowsBefore offset size batch) :
    MixedFlat.readBatch limits schemaBytes (batch.range.metadataSlice input) (batch.range.bodySlice input) =
      .ok batch.observed :=
  Proofs.Formats.Arrow.MixedFlat.Stream.record_decode schema wire

/-- Replaying standalone decoding over the returned ranges recovers the
stream's complete ordered sequence of observations. -/
theorem read_batch_results {limits : MixedFlat.Limits} {input : KBytes} {result : Observed}
    (read : Stream.read limits input = .ok result) :
    ∃ size, readEnvelope limits.observation.ipc input 0 = .ok (.metadata size) ∧
      MixedFlat.readSchema limits.observation.ipc (input.slice 8 size) = .ok result.fields ∧
      (result.batches.mapM fun batch => MixedFlat.readBatch limits (input.slice 8 size)
        (batch.range.metadataSlice input) (batch.range.bodySlice input)) =
        .ok (result.batches.map Batch.observed) :=
  Proofs.Formats.Arrow.MixedFlat.Stream.read_batch_results read

end Silmaril.Formats.Arrow.MixedFlat.Stream
