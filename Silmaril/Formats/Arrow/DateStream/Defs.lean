module

public import Silmaril.Formats.Arrow.DateBatch.Defs

/-! # Bounded Arrow IPC streams with one flat DATE column -/

@[expose] public section

namespace Silmaril.Formats.Arrow.DateStream

structure Field where
  name : String
  nullable : Bool
  unit : SchemaReader.DateUnit
  deriving DecidableEq, Repr

def Field.decoder (field : Field) : DateValues.Unit :=
  DateBatch.dateDecoder field.unit

def Field.descriptor (field : Field) : DateValues.Descriptor :=
  DateBatch.descriptor .little field.unit field.nullable

inductive BatchError where
  | envelope (cause : Arrow.Error)
  | trailingBytes
  | batchLimit
  | metadata (cause : Arrow.Error)
  | expectedRecordBatch
  | body (cause : Arrow.Error)
  | values (cause : DateValues.Error)
  deriving DecidableEq, Repr

inductive Error where
  | source
  | schemaEnvelope (cause : Arrow.Error)
  | expectedSchema
  | schemaMetadata (cause : Arrow.Error)
  | fieldCount (actual : Nat)
  | fieldType (actual : Arrow.FieldType)
  | bigEndian
  | batch (index : Nat) (cause : BatchError)
  deriving DecidableEq, Repr

structure Stream where
  field : Field
  batches : List DateValues.Column
  deriving DecidableEq, Repr

/-- Check the first frame and retain the normalized DATE field once for the stream. -/
def readSchema (limits : Limits) (input : KBytes) : Except Error (Field × Nat) := do
  let envelope ← (readEnvelope limits input 0).mapError .schemaEnvelope
  let .metadata size := envelope | .error .expectedSchema
  let schema ← (SchemaReader.readMessage limits (input.slice 8 size)).mapError .schemaMetadata
  if schema.endianness = .big then .error .bigEndian
  else
    let [field] := schema.fields | .error (.fieldCount schema.fields.length)
    match field.type with
    | .primitive kind => .error (.fieldType kind)
    | .date unit => .ok (⟨field.name, field.nullable, unit⟩, 8 + size)

/-- Decode the record after admitting its envelope. The record's own declared
body length determines both this batch's body and the next frame offset. -/
def readBatch (limits : Limits) (input : KBytes) (field : Field) (offset size : Nat) :
    Except BatchError (DateValues.Column × Nat) := do
  let bodyStart := offset + 8 + size
  let message ← (Arrow.readMessage limits (input.slice (offset + 8) size)).mapError .metadata
  let .recordBatch batch := message.header | .error .expectedRecordBatch
  let body ← (readBody limits input bodyStart message.bodyLength).mapError .body
  let dates ← (DateValues.decodeBatch limits field.decoder field.descriptor batch body).mapError .values
  return (dates, bodyStart + message.bodyLength)

/-- Read a suffix with an explicit batch budget and a zero-based error index. -/
def readBatches (limits : Limits) (input : KBytes) (field : Field) :
    (remaining index offset : Nat) → Except Error (List DateValues.Column)
  | remaining, index, offset => do
    let envelope ← (readEnvelope limits input offset).mapError fun cause => .batch index (.envelope cause)
    match envelope with
    | .eos =>
      if offset + 8 = input.len then .ok [] else .error (.batch index .trailingBytes)
    | .metadata size =>
      match remaining with
      | 0 => .error (.batch index .batchLimit)
      | fuel + 1 =>
        let (dates, next) ← (readBatch limits input field offset size).mapError (.batch index)
        let tail ← readBatches limits input field fuel (index + 1) next
        return dates :: tail

/-- Consume the exact source up to its explicit modern EOS. Failures carry
their stage and, after the schema, the index of the batch being attempted. -/
def read (limits : Limits) (input : KBytes) : Except Error Stream := do
  if !input.wf then .error .source
  else
    let (field, start) ← readSchema limits input
    let batches ← readBatches limits input field limits.batches 0 start
    return ⟨field, batches⟩

/-- Ordered frames through exact EOS, starting at a checked frame boundary. -/
inductive BatchesWire (limits : Limits) (input : KBytes) (field : Field) :
    Nat → Nat → List DateValues.Column → Prop where
  | eos {remaining offset} :
      readEnvelope limits input offset = .ok .eos → offset + 8 = input.len →
      BatchesWire limits input field remaining offset []
  | next {fuel offset size next dates tail} :
      readEnvelope limits input offset = .ok (.metadata size) →
      readBatch limits input field offset size = .ok (dates, next) →
      BatchesWire limits input field fuel next tail →
      BatchesWire limits input field (fuel + 1) offset (dates :: tail)

/-- A suffix failure at the given stream index after fully decoded preceding batches. -/
inductive BatchFailure (limits : Limits) (input : KBytes) (field : Field) :
    Nat → Nat → Nat → Nat → BatchError → Prop where
  | envelope {remaining index offset cause} :
      readEnvelope limits input offset = .error cause →
      BatchFailure limits input field remaining index offset index (.envelope cause)
  | trailing {remaining index offset} :
      readEnvelope limits input offset = .ok .eos → offset + 8 ≠ input.len →
      BatchFailure limits input field remaining index offset index .trailingBytes
  | limit {index offset size} :
      readEnvelope limits input offset = .ok (.metadata size) →
      BatchFailure limits input field 0 index offset index .batchLimit
  | record {fuel index offset size cause} :
      readEnvelope limits input offset = .ok (.metadata size) →
      readBatch limits input field offset size = .error cause →
      BatchFailure limits input field (fuel + 1) index offset index cause
  | next {fuel index offset size dates next failed cause} :
      readEnvelope limits input offset = .ok (.metadata size) →
      readBatch limits input field offset size = .ok (dates, next) →
      BatchFailure limits input field fuel (index + 1) next failed cause →
      BatchFailure limits input field (fuel + 1) index offset failed cause

end Silmaril.Formats.Arrow.DateStream
