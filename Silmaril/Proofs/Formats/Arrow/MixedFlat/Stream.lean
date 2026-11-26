module

public import Silmaril.Formats.Arrow.MixedFlat.Stream.Defs
import Silmaril.Formats.Arrow.Framing.Thms

@[expose] public section

namespace Silmaril.Proofs.Formats.Arrow.MixedFlat.Stream

open Silmaril.Formats
open Silmaril.Formats.Arrow
open Silmaril.Formats.Arrow.MixedFlat (Metadata readMetadata readParsed)
open Silmaril.Formats.Arrow.MixedFlat.Stream

theorem readSchemaFrame_iff (ipc : Arrow.Limits) (input : KBytes) (fields : List MixedFlat.Field) (next : Nat) :
    readSchemaFrame ipc input = .ok (fields, next) ↔
      ∃ size, readEnvelope ipc input 0 = .ok (.metadata size) ∧
        MixedFlat.readSchema ipc (input.slice 8 size) = .ok fields ∧ next = 8 + size := by
  cases envelope : readEnvelope ipc input 0 with
  | error => simp [readSchemaFrame, envelope, bind, Except.bind, Except.mapError]
  | ok frame =>
    cases frame with
    | eos => simp [readSchemaFrame, envelope, bind, Except.bind, Except.mapError]
    | metadata size =>
      cases parsed : MixedFlat.readSchema ipc (input.slice 8 size) <;>
        simp [readSchemaFrame, envelope, parsed, bind, Except.bind, Except.mapError,
          pure, Except.pure, eq_comm]

theorem readRecord_iff (limits : MixedFlat.Limits) (input : KBytes) (fields : List MixedFlat.Field)
    (rowsBefore offset size : Nat) (batch : Batch) :
    readRecord limits input fields rowsBefore offset size = .ok batch ↔
      RecordWire limits input fields rowsBefore offset size batch := by
  cases parsed : readMetadata limits.observation.ipc limits.view.dataBuffers limits.totalDataBuffers fields
      (input.slice (offset + 8) size) with
  | error => simp [readRecord, RecordWire, parsed, bind, Except.bind, Except.mapError]
  | ok metadata =>
    cases bounded : readBody limits.observation.ipc input (offset + 8 + size) metadata.bodyLength with
    | error => simp [readRecord, RecordWire, parsed, bounded, BatchRange.bodyStart,
        bind, Except.bind, Except.mapError]
    | ok body =>
      cases budget : Body.checkBudget limits.observation fields.length (rowsBefore + metadata.batch.rowCount) with
      | error => simp [readRecord, RecordWire, parsed, bounded, budget, BatchRange.bodyStart,
          bind, Except.bind, Except.mapError]
      | ok checked =>
        cases checked
        cases decoded : readParsed limits fields metadata body <;> cases batch <;>
          simp [readRecord, RecordWire, parsed, bounded, budget, decoded, BatchRange.bodyStart,
            bind, Except.bind, Except.mapError, pure, Except.pure, eq_comm, and_comm]

theorem readBatches_iff (limits : MixedFlat.Limits) (input : KBytes) (fields : List MixedFlat.Field)
    (remaining index rowsBefore offset : Nat) (batches : List Batch) :
    readBatches limits input fields remaining index rowsBefore offset = .ok batches ↔
      BatchesWire limits input fields remaining rowsBefore offset batches := by
  constructor
  · intro result
    induction remaining generalizing index rowsBefore offset batches with
    | zero =>
      cases envelope : readEnvelope limits.observation.ipc input offset with
      | error => simp [readBatches, envelope, bind, Except.bind, Except.mapError] at result
      | ok frame =>
        cases frame with
        | metadata => simp [readBatches, envelope, bind, Except.bind, Except.mapError] at result
        | eos =>
          by_cases atEnd : offset + 8 = input.len
          · have empty : [] = batches := by
              simpa [readBatches, envelope, atEnd, bind, Except.bind, Except.mapError, pure, Except.pure] using result
            exact empty ▸ BatchesWire.eos envelope atEnd
          · simp [readBatches, envelope, atEnd, bind, Except.bind, Except.mapError] at result
    | succ fuel ih =>
      cases envelope : readEnvelope limits.observation.ipc input offset with
      | error => simp [readBatches, envelope, bind, Except.bind, Except.mapError] at result
      | ok frame =>
        cases frame with
        | eos =>
          by_cases atEnd : offset + 8 = input.len
          · have empty : [] = batches := by
              simpa [readBatches, envelope, atEnd, bind, Except.bind, Except.mapError, pure, Except.pure] using result
            exact empty ▸ BatchesWire.eos envelope atEnd
          · simp [readBatches, envelope, atEnd, bind, Except.bind, Except.mapError] at result
        | metadata size =>
          cases first : readRecord limits input fields rowsBefore offset size with
          | error => simp [readBatches, envelope, first, bind, Except.bind, Except.mapError] at result
          | ok batch =>
            cases tail : readBatches limits input fields fuel (index + 1)
                (rowsBefore + batch.observed.rowCount) batch.range.next with
            | error => simp [readBatches, envelope, first, tail, bind, Except.bind, Except.mapError] at result
            | ok rest =>
              have ordered : batch :: rest = batches := by
                simpa [readBatches, envelope, first, tail, bind, Except.bind,
                  Except.mapError, pure, Except.pure] using result
              exact ordered ▸ BatchesWire.next envelope ((readRecord_iff _ _ _ _ _ _ _).mp first)
                (ih _ _ _ _ tail)
  · intro wire
    induction wire generalizing index with
    | @eos remaining _ _ envelope atEnd =>
      cases remaining <;> simp [readBatches, envelope, atEnd, bind, Except.bind, Except.mapError, pure, Except.pure]
    | next envelope head _ ih =>
      have accepted := (readRecord_iff _ _ _ _ _ _ _).mpr head
      simp [readBatches, envelope, accepted, ih (index + 1), bind, Except.bind, Except.mapError,
        pure, Except.pure]

theorem read_iff (limits : MixedFlat.Limits) (input : KBytes) (result : Observed) :
    MixedFlat.Stream.read limits input = .ok result ↔
      input.wf = true ∧
        ∃ start, readSchemaFrame limits.observation.ipc input = .ok (result.fields, start) ∧
          BatchesWire limits input result.fields limits.observation.ipc.batches 0 start result.batches := by
  rcases result with ⟨fields, batches⟩
  cases wf : input.wf with
  | false => simp [MixedFlat.Stream.read, wf]
  | true =>
    cases schema : readSchemaFrame limits.observation.ipc input with
    | error => simp [MixedFlat.Stream.read, wf, schema, bind, Except.bind]
    | ok result =>
      obtain ⟨declared, start⟩ := result
      by_cases same : declared = fields
      · subst fields
        have law := readBatches_iff limits input declared limits.observation.ipc.batches 0 0 start batches
        cases suffix : readBatches limits input declared limits.observation.ipc.batches 0 0 start with
        | error =>
          simp [suffix] at law
          simp [MixedFlat.Stream.read, wf, schema, suffix, law, bind, Except.bind]
        | ok columns =>
          simp [suffix] at law
          simp [MixedFlat.Stream.read, wf, schema, suffix, ← law, bind, Except.bind, pure, Except.pure]
      · cases suffix : readBatches limits input declared limits.observation.ipc.batches 0 0 start <;>
          simp [MixedFlat.Stream.read, wf, schema, suffix, same, bind, Except.bind, pure, Except.pure]

theorem record_ranges {limits : MixedFlat.Limits} {input : KBytes} {fields : List MixedFlat.Field}
    {rowsBefore offset size : Nat} {batch : Batch} (wf : input.wf = true)
    (envelope : readEnvelope limits.observation.ipc input offset = .ok (.metadata size))
    (wire : RecordWire limits input fields rowsBefore offset size batch) :
    batch.range.offset = offset ∧ batch.range.metadataSize = size ∧
    offset < batch.range.next ∧ batch.range.next ≤ input.len ∧
    (batch.range.metadataSlice input).toList = (input.toList.drop (offset + 8)).take size ∧
    (batch.range.bodySlice input).toList =
      (input.toList.drop batch.range.bodyStart).take batch.range.bodyLength := by
  rcases batch with ⟨range, observed⟩
  obtain ⟨metadata, body, _, bounded, _, _, same⟩ := wire
  change range = _ at same
  subst range
  have fits := (readBody_iff _ _ _ _ _).mp bounded
  refine ⟨rfl, rfl, ?_, fits.2.2.2.1, metadata_exact wf envelope, ?_⟩
  · simp only [BatchRange.next, BatchRange.bodyStart]
    omega
  · change (input.slice (offset + 8 + size) metadata.bodyLength).toList =
      (input.toList.drop (offset + 8 + size)).take metadata.bodyLength
    rw [← fits.2.2.2.2]
    exact (body_exact wf bounded).2

theorem record_decode {limits : MixedFlat.Limits} {input schemaBytes : KBytes} {fields : List MixedFlat.Field}
    {rowsBefore offset size : Nat} {batch : Batch}
    (schema : MixedFlat.readSchema limits.observation.ipc schemaBytes = .ok fields)
    (wire : RecordWire limits input fields rowsBefore offset size batch) :
    MixedFlat.readBatch limits schemaBytes (batch.range.metadataSlice input) (batch.range.bodySlice input) =
      .ok batch.observed := by
  rcases batch with ⟨range, observed⟩
  obtain ⟨metadata, body, parsed, bounded, _, decoded, same⟩ := wire
  change range = _ at same
  subst range
  have exactBody := (readBody_iff _ _ _ _ _).mp bounded
  simp [MixedFlat.readBatch, schema, BatchRange.metadataSlice, BatchRange.bodySlice, BatchRange.bodyStart,
    parsed, ← exactBody.2.2.2.2, decoded, bind, Except.bind, Except.mapError]

private theorem batches_decode {limits : MixedFlat.Limits} {input schemaBytes : KBytes} {fields : List MixedFlat.Field}
    {remaining rowsBefore offset : Nat} {batches : List Batch}
    (schema : MixedFlat.readSchema limits.observation.ipc schemaBytes = .ok fields)
    (wire : BatchesWire limits input fields remaining rowsBefore offset batches) :
    (batches.mapM fun batch => MixedFlat.readBatch limits schemaBytes
      (batch.range.metadataSlice input) (batch.range.bodySlice input)) = .ok (batches.map Batch.observed) := by
  induction wire with
  | eos => rfl
  | next _ record _ ih =>
    simp [List.mapM_cons, record_decode schema record, ih, bind, Except.bind, pure, Except.pure]

theorem read_batch_results {limits : MixedFlat.Limits} {input : KBytes} {result : Observed}
    (read : MixedFlat.Stream.read limits input = .ok result) :
    ∃ size, readEnvelope limits.observation.ipc input 0 = .ok (.metadata size) ∧
      MixedFlat.readSchema limits.observation.ipc (input.slice 8 size) = .ok result.fields ∧
      (result.batches.mapM fun batch => MixedFlat.readBatch limits (input.slice 8 size)
        (batch.range.metadataSlice input) (batch.range.bodySlice input)) =
        .ok (result.batches.map Batch.observed) := by
  obtain ⟨_, start, schemaFrame, wire⟩ := (read_iff _ _ _).mp read
  obtain ⟨size, envelope, schema, _⟩ := (readSchemaFrame_iff _ _ _ _).mp schemaFrame
  exact ⟨size, envelope, schema, batches_decode schema wire⟩

end Silmaril.Proofs.Formats.Arrow.MixedFlat.Stream
