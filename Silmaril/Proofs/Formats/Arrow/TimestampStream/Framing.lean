module

public import Silmaril.Formats.Arrow.TimestampStream.Defs

public section

namespace Silmaril.Proofs.Formats.Arrow.TimestampStream

open Silmaril Silmaril.Formats.Arrow Silmaril.Formats.Arrow.TimestampStream

theorem readSchema_iff (limits : Limits) (input : KBytes) (binding : TimestampBatch.Binding)
    (start : Nat) :
    readSchema limits input = .ok (binding, start) ↔
      ∃ size schema,
        readEnvelope limits input 0 = .ok (.metadata size) ∧
        SchemaReader.readMessage limits (input.slice 8 size) = .ok schema ∧
        TimestampBatch.bindSchema schema = .ok binding ∧ start = 8 + size := by
  cases envelope : readEnvelope limits input 0 with
  | error => simp [readSchema, envelope, bind, Except.bind, Except.mapError]
  | ok value =>
    cases value with
    | eos => simp [readSchema, envelope, bind, Except.bind, Except.mapError]
    | metadata size =>
      cases schemaRead : SchemaReader.readMessage limits (input.slice 8 size) with
      | error => simp [readSchema, envelope, schemaRead, bind, Except.bind, Except.mapError]
      | ok schema =>
        cases bindingRead : TimestampBatch.bindSchema schema <;>
          simp [readSchema, envelope, schemaRead, bindingRead, bind, Except.bind, Except.mapError,
            pure, Except.pure, eq_comm]

theorem readBatch_iff (limits : Limits) (input : KBytes) (binding : TimestampBatch.Binding)
    (offset size : Nat) (slots : TimestampBatch.Column binding) (next : Nat) :
    readBatch limits input binding offset size = .ok (slots, next) ↔
      ∃ batch length body,
        readMessage limits (input.slice (offset + 8) size) = .ok ⟨.recordBatch batch, length⟩ ∧
        readBody limits input (offset + 8 + size) length = .ok body ∧
        TimestampBatch.decodeBatch limits binding ⟨.recordBatch batch, length⟩ body = .ok slots ∧
        next = offset + 8 + size + length := by
  cases recordRead : readMessage limits (input.slice (offset + 8) size) with
  | error => simp [readBatch, recordRead, bind, Except.bind, Except.mapError]
  | ok message =>
    obtain ⟨header, length⟩ := message
    cases header with
    | schema => simp [readBatch, recordRead, bind, Except.bind, Except.mapError]
    | recordBatch batch =>
      cases bodyRead : readBody limits input (offset + 8 + size) length with
      | error => simp [readBatch, recordRead, bodyRead, bind, Except.bind, Except.mapError]
      | ok body =>
        cases values : TimestampBatch.decodeBatch limits binding ⟨.recordBatch batch, length⟩ body <;>
          simp [readBatch, recordRead, bodyRead, values, bind, Except.bind, Except.mapError,
            pure, Except.pure, eq_comm]

theorem readBatches_iff (limits : Limits) (input : KBytes) (binding : TimestampBatch.Binding)
    (remaining index offset : Nat) (batches : List (TimestampBatch.Column binding)) :
    readBatches limits input binding remaining index offset = .ok batches ↔
      BatchesWire limits input binding remaining offset batches := by
  constructor
  · intro decoded
    induction remaining generalizing index offset batches with
    | zero =>
      cases envelope : readEnvelope limits input offset with
      | error => simp [readBatches, envelope, bind, Except.bind, Except.mapError] at decoded
      | ok value =>
        cases value with
        | metadata => simp [readBatches, envelope, bind, Except.bind, Except.mapError] at decoded
        | eos =>
          by_cases exactEnd : offset + 8 = input.len
          · have ordered : [] = batches := by
              simpa [readBatches, envelope, exactEnd, bind, Except.bind, Except.mapError] using decoded
            exact ordered ▸ .eos envelope exactEnd
          · simp [readBatches, envelope, exactEnd, bind, Except.bind, Except.mapError] at decoded
    | succ fuel ih =>
      cases envelope : readEnvelope limits input offset with
      | error => simp [readBatches, envelope, bind, Except.bind, Except.mapError] at decoded
      | ok value =>
        cases value with
        | eos =>
          by_cases exactEnd : offset + 8 = input.len
          · have ordered : [] = batches := by
              simpa [readBatches, envelope, exactEnd, bind, Except.bind, Except.mapError] using decoded
            exact ordered ▸ .eos envelope exactEnd
          · simp [readBatches, envelope, exactEnd, bind, Except.bind, Except.mapError] at decoded
        | metadata size =>
          cases batchRead : readBatch limits input binding offset size with
          | error =>
            simp [readBatches, envelope, batchRead, bind, Except.bind, Except.mapError] at decoded
          | ok result =>
            obtain ⟨slots, next⟩ := result
            cases tailRead : readBatches limits input binding fuel (index + 1) next with
            | error =>
              simp [readBatches, envelope, batchRead, tailRead, bind, Except.bind, Except.mapError]
                at decoded
            | ok tail =>
              have ordered : slots :: tail = batches := by
                simpa [readBatches, envelope, batchRead, tailRead, bind, Except.bind,
                  Except.mapError, pure, Except.pure] using decoded
              exact ordered ▸ .next envelope batchRead (ih _ _ _ tailRead)
  · intro wire
    induction wire generalizing index with
    | @eos remaining _ envelope exactEnd =>
      cases remaining <;> simp [readBatches, envelope, exactEnd, bind, Except.bind, Except.mapError]
    | next envelope batchRead _ ih =>
      simp [readBatches, envelope, batchRead, ih (index + 1), bind, Except.bind, Except.mapError,
        pure, Except.pure]

theorem read_iff (limits : Limits) (input : KBytes) (result : TimestampStream.Stream) :
    TimestampStream.read limits input = .ok result ↔
      input.wf = true ∧
        ∃ start, readSchema limits input = .ok (result.binding, start) ∧
          BatchesWire limits input result.binding limits.batches start result.batches := by
  constructor
  · intro accepted
    cases wellFormed : input.wf with
    | false => simp [TimestampStream.read, wellFormed] at accepted
    | true =>
      cases schemaRead : readSchema limits input with
      | error => simp [TimestampStream.read, wellFormed, schemaRead, bind, Except.bind] at accepted
      | ok schema =>
        obtain ⟨binding, start⟩ := schema
        cases batchRead : readBatches limits input binding limits.batches 0 start with
        | error =>
          simp [TimestampStream.read, wellFormed, schemaRead, batchRead, bind, Except.bind] at accepted
        | ok batches =>
          have same : (⟨binding, batches⟩ : TimestampStream.Stream) = result := by
            simpa [TimestampStream.read, wellFormed, schemaRead, batchRead, bind, Except.bind,
              pure, Except.pure] using accepted
          subst result
          exact ⟨rfl, start, rfl, (readBatches_iff _ _ _ _ _ _ _).mp batchRead⟩
  · rintro ⟨wellFormed, start, schemaRead, wire⟩
    have batchRead := (readBatches_iff limits input result.binding limits.batches 0 start result.batches).mpr wire
    cases result
    simp [TimestampStream.read, wellFormed, schemaRead, batchRead, bind, Except.bind, pure, Except.pure]

end Silmaril.Proofs.Formats.Arrow.TimestampStream
