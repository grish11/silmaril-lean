module

public import Silmaril.Formats.Arrow.BinaryView.Schema.Defs

/-! One BinaryView or Utf8View field in a bounded modern Arrow IPC V5 stream. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.BinaryView.Stream

inductive BatchError where
  | envelope (cause : Arrow.Error)
  | trailingBytes
  | batchLimit
  | metadata (cause : BinaryView.MetadataError)
  | body (cause : Arrow.Error)
  | decode (cause : Batch.Error)
  deriving DecidableEq, Repr

inductive Error where
  | source
  | schemaEnvelope (cause : Arrow.Error)
  | expectedSchema
  | schemaMetadata (cause : Schema.MetadataError)
  | batch (index : Nat) (cause : BatchError)
  deriving DecidableEq, Repr

structure Observed where
  field : Schema.Field
  batches : List (Schema.Values field.kind)

/-- Admit the first envelope and retain its one declared view field. -/
def readSchema (ipc : Arrow.Limits) (input : KBytes) : Except Error (Schema.Field × Nat) := do
  let envelope ← (readEnvelope ipc input 0).mapError .schemaEnvelope
  let .metadata size := envelope | throw .expectedSchema
  let field ← (Schema.readMessage ipc (input.slice 8 size)).mapError .schemaMetadata
  return (field, 8 + size)

/-- After checking an envelope, use the view metadata's declared length to
check the body window and advance through that exact extent. -/
def readBatch (ipc : Arrow.Limits) (limits : Column.Limits) (input : KBytes)
    (field : Schema.Field) (offset size : Nat) :
    Except BatchError (Schema.Values field.kind × Nat) := do
  let metadata ← (readBatchMetadata ipc limits.dataBuffers (input.slice (offset + 8) size)).mapError .metadata
  let bodyStart := offset + 8 + size
  let body ← (readBody ipc input bodyStart metadata.bodyLength).mapError .body
  let values ← (Schema.readParsed ipc limits field metadata body).mapError .decode
  return (values, bodyStart + metadata.bodyLength)

/-- Consume a suffix in order. Errors after the schema report the zero-based
record index, including the position at which an EOS was expected. -/
def readBatches (ipc : Arrow.Limits) (limits : Column.Limits) (input : KBytes)
    (field : Schema.Field) : (remaining index offset : Nat) → Except Error (List (Schema.Values field.kind))
  | remaining, index, offset => do
    let envelope ← (readEnvelope ipc input offset).mapError fun cause => .batch index (.envelope cause)
    match envelope with
    | .eos =>
      if offset + 8 = input.len then return []
      else throw (.batch index .trailingBytes)
    | .metadata size =>
      match remaining with
      | 0 => throw (.batch index .batchLimit)
      | fuel + 1 =>
        let (values, next) ← (readBatch ipc limits input field offset size).mapError (.batch index)
        let rest ← readBatches ipc limits input field fuel (index + 1) next
        return values :: rest

/-- Read the exact carrier through modern EOS. The one checked field governs
every record, including the empty records. -/
def read (ipc : Arrow.Limits) (limits : Column.Limits) (input : KBytes) : Except Error Observed :=
  if !input.wf then .error .source
  else do
    let (field, start) ← readSchema ipc input
    let batches ← readBatches ipc limits input field ipc.batches 0 start
    return ⟨field, batches⟩

/-- A checked view batch uses its declared body range and the standalone
field observation over that same metadata and body. -/
def BatchWire (ipc : Arrow.Limits) (limits : Column.Limits) (input : KBytes)
    (field : Schema.Field) (offset size : Nat) (values : Schema.Values field.kind) (next : Nat) : Prop :=
  let bytes := input.slice (offset + 8) size
  ∃ (metadata : BatchMetadata bytes limits.dataBuffers) (body : KBytes),
    readBatchMetadata ipc limits.dataBuffers bytes = .ok metadata ∧
    readBody ipc input (offset + 8 + size) metadata.bodyLength = .ok body ∧
    Schema.readField ipc limits field bytes body = .ok values ∧
    next = offset + 8 + size + metadata.bodyLength

/-- One ordered observation per RecordBatch; empty observations still consume
one frame and one unit of fuel. -/
inductive BatchesWire (ipc : Arrow.Limits) (limits : Column.Limits) (input : KBytes)
    (field : Schema.Field) : Nat → Nat → List (Schema.Values field.kind) → Prop where
  | eos {remaining offset} :
      readEnvelope ipc input offset = .ok .eos → offset + 8 = input.len →
      BatchesWire ipc limits input field remaining offset []
  | next {fuel offset size next values rest} :
      readEnvelope ipc input offset = .ok (.metadata size) →
      BatchWire ipc limits input field offset size values next →
      BatchesWire ipc limits input field fuel next rest →
      BatchesWire ipc limits input field (fuel + 1) offset (values :: rest)

end Silmaril.Formats.Arrow.BinaryView.Stream
