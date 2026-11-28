module

public import Silmaril.Formats.Arrow.TimestampBatch.Defs

/-! # Bounded Arrow IPC streams with one flat little-endian TIMESTAMP field -/

@[expose] public section

namespace Silmaril.Formats.Arrow.TimestampStream

inductive BatchError where
  | envelope (cause : Arrow.Error)
  | trailingBytes
  | batchLimit
  | metadata (cause : Arrow.Error)
  | expectedRecordBatch
  | body (cause : Arrow.Error)
  | values (cause : Arrow.Error)
  deriving DecidableEq, Repr

inductive Error where
  | source
  | schemaEnvelope (cause : Arrow.Error)
  | expectedSchema
  | schemaMetadata (cause : Arrow.Error)
  | schemaBinding (cause : Arrow.Error)
  | batch (index : Nat) (cause : BatchError)
  deriving DecidableEq, Repr

structure Stream where
  binding : TimestampBatch.Binding
  batches : List (TimestampBatch.Column binding)

/-- Read and bind the first framed Schema once. -/
def readSchema (limits : Limits) (input : KBytes) :
    Except Error (TimestampBatch.Binding × Nat) := do
  let envelope ← (readEnvelope limits input 0).mapError .schemaEnvelope
  let .metadata size := envelope | throw .expectedSchema
  let schema ← (SchemaReader.readMessage limits (input.slice 8 size)).mapError .schemaMetadata
  let binding ← (TimestampBatch.bindSchema schema).mapError .schemaBinding
  return (binding, 8 + size)

/-- At an admitted metadata span, use this record's body extent and the retained binding. -/
def readBatch (limits : Limits) (input : KBytes) (binding : TimestampBatch.Binding)
    (offset size : Nat) : Except BatchError (TimestampBatch.Column binding × Nat) := do
  let bodyStart := offset + 8 + size
  let message ← (Arrow.readMessage limits (input.slice (offset + 8) size)).mapError .metadata
  let .recordBatch _ := message.header | throw .expectedRecordBatch
  let body ← (readBody limits input bodyStart message.bodyLength).mapError .body
  let slots ← (TimestampBatch.decodeBatch limits binding message body).mapError .values
  return (slots, bodyStart + message.bodyLength)

/-- Read the remaining frames with a batch budget and a zero-based error index. -/
def readBatches (limits : Limits) (input : KBytes) (binding : TimestampBatch.Binding) :
    Nat → Nat → Nat → Except Error (List (TimestampBatch.Column binding))
  | remaining, index, offset => do
    let envelope ← (readEnvelope limits input offset).mapError fun cause => .batch index (.envelope cause)
    match envelope with
    | .eos =>
      if offset + 8 = input.len then .ok [] else .error (.batch index .trailingBytes)
    | .metadata size =>
      match remaining with
      | 0 => throw (.batch index .batchLimit)
      | fuel + 1 =>
        let (slots, next) ← (readBatch limits input binding offset size).mapError (.batch index)
        let tail ← readBatches limits input binding fuel (index + 1) next
        return slots :: tail

/-- Consume a complete modern IPC stream, including the final EOS marker. -/
def read (limits : Limits) (input : KBytes) : Except Error Stream :=
  if !input.wf then .error .source
  else do
    let (binding, start) ← readSchema limits input
    let batches ← readBatches limits input binding limits.batches 0 start
    return ⟨binding, batches⟩

/-- One column per record frame in byte order. A zero-row frame still contributes
an empty column. The final EOS occupies exactly the rest of the input. -/
inductive BatchesWire (limits : Limits) (input : KBytes) (binding : TimestampBatch.Binding) :
    Nat → Nat → List (TimestampBatch.Column binding) → Prop where
  | eos {remaining offset} :
      readEnvelope limits input offset = .ok .eos → offset + 8 = input.len →
      BatchesWire limits input binding remaining offset []
  | next {fuel offset size nextOffset slots tail} :
      readEnvelope limits input offset = .ok (.metadata size) →
      readBatch limits input binding offset size = .ok (slots, nextOffset) →
      BatchesWire limits input binding fuel nextOffset tail →
      BatchesWire limits input binding (fuel + 1) offset (slots :: tail)

end Silmaril.Formats.Arrow.TimestampStream
