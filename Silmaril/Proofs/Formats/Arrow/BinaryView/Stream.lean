module

public import Silmaril.Formats.Arrow.BinaryView.Stream.Defs
import Silmaril.Formats.Arrow.Framing.Thms

@[expose] public section

namespace Silmaril.Proofs.Formats.Arrow.BinaryView.Stream

open Silmaril.Formats
open Silmaril.Formats.Arrow
open Silmaril.Formats.Arrow.BinaryView
open Silmaril.Formats.Arrow.BinaryView.Stream

theorem readSchema_iff (ipc : Arrow.Limits) (input : KBytes) (field : Schema.Field) (next : Nat) :
    readSchema ipc input = .ok (field, next) ↔
      ∃ size, readEnvelope ipc input 0 = .ok (.metadata size) ∧
        Schema.readMessage ipc (input.slice 8 size) = .ok field ∧ next = 8 + size := by
  cases envelope : readEnvelope ipc input 0 with
  | error => simp [readSchema, envelope, bind, Except.bind, Except.mapError]
  | ok first =>
    cases first with
    | eos => simp [readSchema, envelope, bind, Except.bind, Except.mapError]
    | metadata size =>
      cases parsed : Schema.readMessage ipc (input.slice 8 size) <;>
        simp [readSchema, envelope, parsed, bind, Except.bind, Except.mapError, pure, Except.pure, eq_comm]

private theorem readField_of_parsed (ipc : Arrow.Limits) (limits : Column.Limits)
    (field : Schema.Field) {bytes body : KBytes} {metadata : BatchMetadata bytes limits.dataBuffers}
    (parsed : readBatchMetadata ipc limits.dataBuffers bytes = .ok metadata) :
    Schema.readField ipc limits field bytes body = Schema.readParsed ipc limits field metadata body := by
  rcases field with ⟨name, nullable, kind⟩
  cases bound : Batch.bindParsed ipc nullable metadata body <;> cases kind <;>
    simp [Schema.readField, Schema.readParsed, Batch.readBinary, Batch.readUtf8, Batch.bindBuffers,
      parsed, bound, bind, Except.bind, Except.mapError] <;> rfl

theorem readBatch_iff (ipc : Arrow.Limits) (limits : Column.Limits) (input : KBytes)
    (field : Schema.Field) (offset size : Nat) (values : Schema.Values field.kind) (next : Nat) :
    readBatch ipc limits input field offset size = .ok (values, next) ↔
      Stream.BatchWire ipc limits input field offset size values next := by
  cases parsed : readBatchMetadata ipc limits.dataBuffers (input.slice (offset + 8) size) with
  | error => simp [readBatch, Stream.BatchWire, parsed, bind, Except.bind, Except.mapError]
  | ok metadata =>
    cases bounded : readBody ipc input (offset + 8 + size) metadata.bodyLength with
    | error => simp [readBatch, Stream.BatchWire, parsed, bounded, bind, Except.bind, Except.mapError]
    | ok body =>
      have fieldRead := readField_of_parsed ipc limits field (body := body) parsed
      cases decoded : Schema.readParsed ipc limits field metadata body <;>
        simp [readBatch, Stream.BatchWire, parsed, bounded, fieldRead, decoded, bind, Except.bind,
          Except.mapError, pure, Except.pure, eq_comm]

theorem readBatches_iff (ipc : Arrow.Limits) (limits : Column.Limits) (input : KBytes)
    (field : Schema.Field) (remaining index offset : Nat) (batches : List (Schema.Values field.kind)) :
    readBatches ipc limits input field remaining index offset = .ok batches ↔
      BatchesWire ipc limits input field remaining offset batches := by
  constructor
  · intro result
    induction remaining generalizing index offset batches with
    | zero =>
      cases envelope : readEnvelope ipc input offset with
      | error => simp [readBatches, envelope, bind, Except.bind, Except.mapError] at result
      | ok value =>
        cases value with
        | metadata => simp [readBatches, envelope, bind, Except.bind, Except.mapError] at result
        | eos =>
          by_cases atEnd : offset + 8 = input.len
          · have empty : [] = batches := by
              simpa [readBatches, envelope, atEnd, bind, Except.bind, Except.mapError, pure, Except.pure] using result
            exact empty ▸ BatchesWire.eos envelope atEnd
          · simp [readBatches, envelope, atEnd, bind, Except.bind, Except.mapError] at result
    | succ fuel ih =>
      cases envelope : readEnvelope ipc input offset with
      | error => simp [readBatches, envelope, bind, Except.bind, Except.mapError] at result
      | ok value =>
        cases value with
        | eos =>
          by_cases atEnd : offset + 8 = input.len
          · have empty : [] = batches := by
              simpa [readBatches, envelope, atEnd, bind, Except.bind, Except.mapError, pure, Except.pure] using result
            exact empty ▸ BatchesWire.eos envelope atEnd
          · simp [readBatches, envelope, atEnd, bind, Except.bind, Except.mapError] at result
        | metadata size =>
          cases batchRead : readBatch ipc limits input field offset size with
          | error => simp [readBatches, envelope, batchRead, bind, Except.bind, Except.mapError] at result
          | ok pair =>
            obtain ⟨values, next⟩ := pair
            cases restRead : readBatches ipc limits input field fuel (index + 1) next with
            | error =>
              simp [readBatches, envelope, batchRead, restRead, bind, Except.bind, Except.mapError] at result
            | ok rest =>
              have ordered : values :: rest = batches := by
                simpa [readBatches, envelope, batchRead, restRead, bind, Except.bind,
                  Except.mapError, pure, Except.pure] using result
              exact ordered ▸ BatchesWire.next envelope
                ((readBatch_iff _ _ _ _ _ _ _ _).mp batchRead) (ih _ _ _ restRead)
  · intro wire
    induction wire generalizing index with
    | @eos remaining _ envelope atEnd =>
      cases remaining <;> simp [readBatches, envelope, atEnd, bind, Except.bind, Except.mapError, pure, Except.pure]
    | next envelope batch _ ih =>
      have accepted := (readBatch_iff _ _ _ _ _ _ _ _).mpr batch
      simp [readBatches, envelope, accepted, ih (index + 1), bind, Except.bind, Except.mapError,
        pure, Except.pure]

theorem read_iff (ipc : Arrow.Limits) (limits : Column.Limits) (input : KBytes) (result : Observed) :
    Stream.read ipc limits input = .ok result ↔
      input.wf = true ∧
        ∃ start, readSchema ipc input = .ok (result.field, start) ∧
          BatchesWire ipc limits input result.field ipc.batches start result.batches := by
  rcases result with ⟨field, batches⟩
  cases wf : input.wf with
  | false => simp [Stream.read, wf]
  | true =>
    cases schemaRead : readSchema ipc input with
    | error => simp [Stream.read, wf, schemaRead, bind, Except.bind]
    | ok schema =>
      obtain ⟨observed, start⟩ := schema
      by_cases same : observed = field
      · subst field
        have law := readBatches_iff ipc limits input observed ipc.batches 0 start batches
        cases suffix : readBatches ipc limits input observed ipc.batches 0 start with
        | error =>
          simp [suffix] at law
          simp [Stream.read, wf, schemaRead, suffix, law, bind, Except.bind]
        | ok columns =>
          simp [suffix] at law
          simp [Stream.read, wf, schemaRead, suffix, ← law, bind, Except.bind, pure, Except.pure]
      · cases suffix : readBatches ipc limits input observed ipc.batches 0 start <;>
          simp [Stream.read, wf, schemaRead, suffix, same, bind, Except.bind, pure, Except.pure]

theorem batches_length_le {ipc : Arrow.Limits} {limits : Column.Limits} {input : KBytes}
    {field : Schema.Field} {remaining offset : Nat} {batches : List (Schema.Values field.kind)}
    (wire : BatchesWire ipc limits input field remaining offset batches) : batches.length ≤ remaining := by
  induction wire with
  | eos => exact Nat.zero_le _
  | next _ _ _ bound => exact Nat.succ_le_succ bound

theorem batch_ranges {ipc : Arrow.Limits} {limits : Column.Limits} {input : KBytes}
    {field : Schema.Field} {offset size next : Nat} {values : Schema.Values field.kind}
    (wf : input.wf = true) (envelope : readEnvelope ipc input offset = .ok (.metadata size))
    (wire : Stream.BatchWire ipc limits input field offset size values next) :
    offset < next ∧ next ≤ input.len ∧
      (input.slice (offset + 8) size).toList = (input.toList.drop (offset + 8)).take size ∧
      ∃ body, body.toList = (input.toList.drop (offset + 8 + size)).take (next - (offset + 8 + size)) ∧
        Schema.readField ipc limits field (input.slice (offset + 8) size) body = .ok values := by
  obtain ⟨metadata, body, _, bounded, observed, rfl⟩ := wire
  have fits := (readBody_iff _ _ _ _ _).mp bounded
  have extent := (body_exact wf bounded).2
  refine ⟨by omega, fits.2.2.2.1, metadata_exact wf envelope, body, ?_, observed⟩
  simpa using extent

end Silmaril.Proofs.Formats.Arrow.BinaryView.Stream
