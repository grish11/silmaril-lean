module

public import Silmaril.Formats.Arrow.DateStream.Defs
import Silmaril.Formats.Arrow.DateValues.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.DateStream

open Silmaril Silmaril.Formats.Arrow Silmaril.Formats.Arrow.DateStream

theorem readSchema_iff (limits : Limits) (input : KBytes) (field : DateStream.Field)
    (start : Nat) :
    readSchema limits input = .ok (field, start) ↔
      ∃ size,
        readEnvelope limits input 0 = .ok (.metadata size) ∧ start = 8 + size ∧
        SchemaReader.readMessage limits (input.slice 8 size) =
          .ok ⟨.little, [⟨field.name, field.nullable, .date field.unit⟩]⟩ := by
  cases envelope : readEnvelope limits input 0 with
  | error => simp [readSchema, envelope, bind, Except.bind, Except.mapError]
  | ok firstEnvelope =>
    cases firstEnvelope with
    | eos => simp [readSchema, envelope, bind, Except.bind, Except.mapError]
    | metadata size =>
      cases schemaRead : SchemaReader.readMessage limits (input.slice 8 size) with
      | error => simp [readSchema, envelope, schemaRead, bind, Except.bind, Except.mapError]
      | ok schema =>
        obtain ⟨endian, fields⟩ := schema
        cases endian with
        | big => simp [readSchema, envelope, schemaRead, bind, Except.bind, Except.mapError]
        | little =>
          cases fields with
          | nil => simp [readSchema, envelope, schemaRead, bind, Except.bind, Except.mapError]
          | cons first tail =>
            cases tail with
            | cons next tail => simp [readSchema, envelope, schemaRead, bind, Except.bind, Except.mapError]
            | nil =>
              obtain ⟨name, nullable, kind⟩ := first
              cases field
              cases kind <;>
                simp [readSchema, envelope, schemaRead, DateBatch.selectDateUnit, bind, Except.bind,
                  Except.mapError, pure, Except.pure]; grind

theorem readBatch_iff (limits : Limits) (input : KBytes) (field : DateStream.Field)
    (offset size : Nat) (dates : DateValues.Column) (next : Nat) :
    readBatch limits input field offset size = .ok (dates, next) ↔
      ∃ batch length body view,
        readMessage limits (input.slice (offset + 8) size) = .ok ⟨.recordBatch batch, length⟩ ∧
        readBody limits input (offset + 8 + size) length = .ok body ∧
        next = offset + 8 + size + length ∧
        DateValues.batchView limits batch body = .ok view ∧
        DateValues.check limits field.decoder field.descriptor view = .ok () ∧
        DateValues.ColumnWire field.decoder view dates := by
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
        have values := DateValues.decodeBatch_iff limits field.decoder field.descriptor batch body dates
        cases decoded : DateValues.decodeBatch limits field.decoder field.descriptor batch body with
        | error =>
          constructor
          · simp [readBatch, recordRead, bodyRead, decoded, bind, Except.bind, Except.mapError]
          · rintro ⟨_, _, supplied, view, recordEq, bodyEq, _, arranged, checked, observed⟩
            cases recordEq
            have same : body = supplied := Except.ok.inj (bodyRead.symm.trans bodyEq)
            subst supplied
            have accepted := values.mpr ⟨view, arranged, checked, observed⟩
            rw [decoded] at accepted
            contradiction
        | ok observations =>
          constructor
          · intro decodedBatch
            have same : observations = dates ∧ offset + 8 + size + length = next := by
              simpa [readBatch, recordRead, bodyRead, decoded, bind, Except.bind, Except.mapError,
                pure, Except.pure] using decodedBatch
            obtain ⟨view, arranged, checked, observed⟩ :=
              values.mp (decoded.trans (congrArg Except.ok same.1))
            exact ⟨batch, length, body, view, rfl, bodyRead, same.2.symm, arranged, checked, observed⟩
          · rintro ⟨_, _, supplied, view, recordEq, bodyEq, offsetEq, arranged, checked, observed⟩
            cases recordEq
            have same : body = supplied := Except.ok.inj (bodyRead.symm.trans bodyEq)
            subst supplied
            have ordered := Except.ok.inj (decoded.symm.trans (values.mpr ⟨view, arranged, checked, observed⟩))
            simp [readBatch, recordRead, bodyRead, decoded, ordered, offsetEq, bind, Except.bind,
              Except.mapError, pure, Except.pure]


theorem readBatches_iff (limits : Limits) (input : KBytes) (field : DateStream.Field)
    (remaining index offset : Nat) (batches : List DateValues.Column) :
    readBatches limits input field remaining index offset = .ok batches ↔
      BatchesWire limits input field remaining offset batches := by
  constructor
  · intro decoded
    induction remaining generalizing index offset batches with
    | zero =>
      cases envelope : readEnvelope limits input offset with
      | error => simp [readBatches, envelope, bind, Except.bind, Except.mapError] at decoded
      | ok envelopeValue =>
        cases envelopeValue with
        | metadata => simp [readBatches, envelope, bind, Except.bind, Except.mapError] at decoded
        | eos =>
          by_cases exactEnd : offset + 8 = input.len
          · have empty : [] = batches := by
              simpa [readBatches, envelope, exactEnd, bind, Except.bind, Except.mapError] using decoded
            exact empty ▸ BatchesWire.eos envelope exactEnd
          · simp [readBatches, envelope, exactEnd, bind, Except.bind, Except.mapError] at decoded
    | succ fuel ih =>
      cases envelope : readEnvelope limits input offset with
      | error => simp [readBatches, envelope, bind, Except.bind, Except.mapError] at decoded
      | ok envelopeValue =>
        cases envelopeValue with
        | eos =>
          by_cases exactEnd : offset + 8 = input.len
          · have empty : [] = batches := by
              simpa [readBatches, envelope, exactEnd, bind, Except.bind, Except.mapError] using decoded
            exact empty ▸ BatchesWire.eos envelope exactEnd
          · simp [readBatches, envelope, exactEnd, bind, Except.bind, Except.mapError] at decoded
        | metadata size =>
          cases batchRead : readBatch limits input field offset size with
          | error => simp [readBatches, envelope, batchRead, bind, Except.bind, Except.mapError] at decoded
          | ok pair =>
            obtain ⟨dates, next⟩ := pair
            cases restRead : readBatches limits input field fuel (index + 1) next with
            | error =>
              simp [readBatches, envelope, batchRead, restRead, bind, Except.bind, Except.mapError]
                at decoded
            | ok rest =>
              have ordered : dates :: rest = batches := by
                simpa [readBatches, envelope, batchRead, restRead, bind, Except.bind,
                  Except.mapError, pure, Except.pure] using decoded
              exact ordered ▸ BatchesWire.next envelope batchRead (ih _ _ _ restRead)
  · intro wire
    induction wire generalizing index with
    | @eos remaining _ envelope exactEnd =>
      cases remaining <;>
        simp [readBatches, envelope, exactEnd, bind, Except.bind, Except.mapError]
    | next envelope batchRead _ ih =>
      simp [readBatches, envelope, batchRead, ih (index + 1), bind, Except.bind, Except.mapError,
        pure, Except.pure]

theorem readBatches_error_iff (limits : Limits) (input : KBytes) (field : DateStream.Field)
    (remaining index offset failed : Nat) (cause : BatchError) :
    readBatches limits input field remaining index offset = .error (.batch failed cause) ↔
      BatchFailure limits input field remaining index offset failed cause := by
  constructor
  · intro decoded
    induction remaining generalizing index offset with
    | zero =>
      cases envelope : readEnvelope limits input offset with
      | error error =>
        have same : DateStream.Error.batch index (.envelope error) = .batch failed cause := by
          simpa only [readBatches, envelope, bind, Except.bind, Except.mapError, Except.error.injEq] using decoded
        cases same
        exact .envelope envelope
      | ok envelopeValue =>
        cases envelopeValue with
        | eos =>
          by_cases exactEnd : offset + 8 = input.len
          · simp [readBatches, envelope, exactEnd, bind, Except.bind, Except.mapError] at decoded
          · have same : DateStream.Error.batch index .trailingBytes = .batch failed cause := by
              simpa [readBatches, envelope, exactEnd, bind, Except.bind, Except.mapError] using decoded
            cases same
            exact .trailing envelope exactEnd
        | metadata size =>
          have same : DateStream.Error.batch index .batchLimit = .batch failed cause := by
            simpa only [readBatches, envelope, bind, Except.bind, Except.mapError, Except.error.injEq] using decoded
          cases same
          exact .limit envelope
    | succ fuel ih =>
      cases envelope : readEnvelope limits input offset with
      | error error =>
        have same : DateStream.Error.batch index (.envelope error) = .batch failed cause := by
          simpa only [readBatches, envelope, bind, Except.bind, Except.mapError, Except.error.injEq] using decoded
        cases same
        exact .envelope envelope
      | ok envelopeValue =>
        cases envelopeValue with
        | eos =>
          by_cases exactEnd : offset + 8 = input.len
          · simp [readBatches, envelope, exactEnd, bind, Except.bind, Except.mapError] at decoded
          · have same : DateStream.Error.batch index .trailingBytes = .batch failed cause := by
              simpa [readBatches, envelope, exactEnd, bind, Except.bind, Except.mapError] using decoded
            cases same
            exact .trailing envelope exactEnd
        | metadata size =>
          cases batchRead : readBatch limits input field offset size with
          | error error =>
            have same : DateStream.Error.batch index error = .batch failed cause := by
              simpa only [readBatches, envelope, batchRead, bind, Except.bind, Except.mapError,
                Except.error.injEq] using decoded
            cases same
            exact .record envelope batchRead
          | ok pair =>
            obtain ⟨dates, next⟩ := pair
            cases restRead : readBatches limits input field fuel (index + 1) next with
            | error error =>
              have same : error = .batch failed cause := by
                simpa only [readBatches, envelope, batchRead, restRead, bind, Except.bind,
                  Except.mapError, Except.error.injEq] using decoded
              exact .next envelope batchRead (ih _ _ (restRead.trans (congrArg Except.error same)))
            | ok rest =>
              simp [readBatches, envelope, batchRead, restRead, bind, Except.bind, Except.mapError,
                pure, Except.pure] at decoded
  · intro wire
    induction wire with
    | @envelope remaining _ _ _ envelope =>
      cases remaining <;> simp [readBatches, envelope, bind, Except.bind, Except.mapError]
    | @trailing remaining _ _ envelope exactEnd =>
      cases remaining <;> simp [readBatches, envelope, exactEnd, bind, Except.bind, Except.mapError]
    | limit envelope =>
      simp [readBatches, envelope, bind, Except.bind, Except.mapError]
    | record envelope batchRead =>
      simp [readBatches, envelope, batchRead, bind, Except.bind, Except.mapError]
    | next envelope batchRead _ ih =>
      simp [readBatches, envelope, batchRead, ih, bind, Except.bind, Except.mapError]

theorem read_iff (limits : Limits) (input : KBytes) (result : DateStream.Stream) :
    DateStream.read limits input = .ok result ↔
      input.wf = true ∧
        ∃ start, readSchema limits input = .ok (result.field, start) ∧
          BatchesWire limits input result.field limits.batches start result.batches := by
  rcases result with ⟨field, batches⟩
  cases wellFormed : input.wf with
  | false => simp [DateStream.read, wellFormed]
  | true =>
    cases schemaRead : readSchema limits input with
    | error => simp [DateStream.read, wellFormed, schemaRead, bind, Except.bind]
    | ok schema =>
      obtain ⟨observed, start⟩ := schema
      by_cases same : observed = field
      · subst field
        have batchLaw := readBatches_iff limits input observed limits.batches 0 start batches
        cases batchRead : readBatches limits input observed limits.batches 0 start with
        | error =>
          simp [batchRead] at batchLaw
          simp [DateStream.read, wellFormed, schemaRead, batchRead, batchLaw, bind, Except.bind]
        | ok columns =>
          simp [batchRead] at batchLaw
          simp [DateStream.read, wellFormed, schemaRead, batchRead, ← batchLaw, bind, Except.bind,
            pure, Except.pure]
      · cases batchRead : readBatches limits input observed limits.batches 0 start <;>
          simp [DateStream.read, wellFormed, schemaRead, batchRead, same, bind, Except.bind,
            pure, Except.pure]

theorem read_batch_error_iff {limits : Limits} {input : KBytes} {field : DateStream.Field}
    {start : Nat} (wellFormed : input.wf = true)
    (schema : readSchema limits input = .ok (field, start)) (failed : Nat) (cause : BatchError) :
    DateStream.read limits input = .error (.batch failed cause) ↔
      BatchFailure limits input field limits.batches 0 start failed cause := by
  rw [← readBatches_error_iff]
  cases suffix : readBatches limits input field limits.batches 0 start <;>
    simp [DateStream.read, wellFormed, schema, suffix, bind, Except.bind, pure, Except.pure]

end Silmaril.Proofs.Formats.Arrow.DateStream
