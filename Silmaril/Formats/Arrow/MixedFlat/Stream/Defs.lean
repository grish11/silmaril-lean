module

public import Silmaril.Formats.Arrow.MixedFlat.Defs

/-! Flat mixed Arrow IPC V5 streams with exact framed record ranges. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.MixedFlat.Stream

structure BatchRange where
  offset : Nat
  metadataSize : Nat
  bodyLength : Nat
  deriving DecidableEq, Repr

def BatchRange.bodyStart (range : BatchRange) : Nat :=
  range.offset + 8 + range.metadataSize

def BatchRange.next (range : BatchRange) : Nat :=
  range.bodyStart + range.bodyLength

def BatchRange.metadataSlice (range : BatchRange) (input : KBytes) : KBytes :=
  input.slice (range.offset + 8) range.metadataSize

def BatchRange.bodySlice (range : BatchRange) (input : KBytes) : KBytes :=
  input.slice range.bodyStart range.bodyLength

structure Batch where
  range : BatchRange
  observed : MixedFlat.Observed

structure Observed where
  fields : List Field
  batches : List Batch

inductive BatchError where
  | envelope (cause : Arrow.Error)
  | trailingBytes
  | batchLimit
  | metadata (cause : MixedFlat.MetadataError)
  | body (cause : Arrow.Error)
  | budget (cause : Arrow.Error)
  | decode (cause : MixedFlat.Error)
  deriving DecidableEq, Repr

inductive Error where
  | source
  | schemaEnvelope (cause : Arrow.Error)
  | expectedSchema
  | schemaMetadata (cause : Arrow.Error)
  | batch (index : Nat) (cause : BatchError)
  deriving DecidableEq, Repr

/-- Admit the first frame's field list and advance past its padded metadata. -/
def readSchemaFrame (ipc : Arrow.Limits) (input : KBytes) : Except Error (List Field × Nat) := do
  let envelope ← (readEnvelope ipc input 0).mapError .schemaEnvelope
  let .metadata size := envelope | throw .expectedSchema
  let fields ← (MixedFlat.readSchema ipc (input.slice 8 size)).mapError .schemaMetadata
  return (fields, 8 + size)

/-- Read a RecordBatch after its envelope is admitted. Check the running
stream row and cell budgets before invoking the column decoders. -/
def readRecord (limits : MixedFlat.Limits) (input : KBytes) (fields : List Field)
    (rowsBefore offset size : Nat) : Except BatchError Batch := do
  let ipc := limits.observation.ipc
  let metadata ← (readMetadata ipc limits.view.dataBuffers limits.totalDataBuffers fields
    (input.slice (offset + 8) size)).mapError .metadata
  let range : BatchRange := ⟨offset, size, metadata.bodyLength⟩
  let body ← (readBody ipc input range.bodyStart range.bodyLength).mapError .body
  (Body.checkBudget limits.observation fields.length (rowsBefore + metadata.batch.rowCount)).mapError .budget
  let observed ← (readParsed limits fields metadata body).mapError .decode
  return ⟨range, observed⟩

/-- Decode each frame in order. The zero-based batch index also identifies
the position where EOS was expected. -/
def readBatches (limits : MixedFlat.Limits) (input : KBytes) (fields : List Field) :
    (remaining index rowsBefore offset : Nat) → Except Error (List Batch)
  | remaining, index, rowsBefore, offset => do
    let envelope ← (readEnvelope limits.observation.ipc input offset).mapError
      fun cause => .batch index (.envelope cause)
    match envelope with
    | .eos =>
      if offset + 8 = input.len then return []
      else throw (.batch index .trailingBytes)
    | .metadata size =>
      match remaining with
      | 0 => throw (.batch index .batchLimit)
      | fuel + 1 =>
        let batch ← (readRecord limits input fields rowsBefore offset size).mapError (.batch index)
        let rest ← readBatches limits input fields fuel (index + 1)
          (rowsBefore + batch.observed.rowCount) batch.range.next
        return batch :: rest

/-- Parse the Schema once and retain every checked record range through exact
modern EOS, including zero-row batches. -/
def read (limits : MixedFlat.Limits) (input : KBytes) : Except Error Observed :=
  if !input.wf then .error .source
  else do
    let (fields, offset) ← readSchemaFrame limits.observation.ipc input
    let batches ← readBatches limits input fields limits.observation.ipc.batches 0 0 offset
    return ⟨fields, batches⟩

def RecordWire (limits : MixedFlat.Limits) (input : KBytes) (fields : List Field)
    (rowsBefore offset size : Nat) (batch : Batch) : Prop :=
  ∃ metadata body,
    readMetadata limits.observation.ipc limits.view.dataBuffers limits.totalDataBuffers fields
      (input.slice (offset + 8) size) = .ok metadata ∧
    readBody limits.observation.ipc input (offset + 8 + size) metadata.bodyLength = .ok body ∧
    Body.checkBudget limits.observation fields.length (rowsBefore + metadata.batch.rowCount) = .ok () ∧
    readParsed limits fields metadata body = .ok batch.observed ∧
    batch.range = ⟨offset, size, metadata.bodyLength⟩

/-- The ranges consume successive admitted envelopes through the exact final
EOS. Each accepted frame contributes one observation. -/
inductive BatchesWire (limits : MixedFlat.Limits) (input : KBytes) (fields : List Field) :
    Nat → Nat → Nat → List Batch → Prop where
  | eos {remaining rowsBefore offset} :
      readEnvelope limits.observation.ipc input offset = .ok .eos → offset + 8 = input.len →
      BatchesWire limits input fields remaining rowsBefore offset []
  | next {fuel rowsBefore offset size batch rest} :
      readEnvelope limits.observation.ipc input offset = .ok (.metadata size) →
      RecordWire limits input fields rowsBefore offset size batch →
      BatchesWire limits input fields fuel (rowsBefore + batch.observed.rowCount) batch.range.next rest →
      BatchesWire limits input fields (fuel + 1) rowsBefore offset (batch :: rest)

end Silmaril.Formats.Arrow.MixedFlat.Stream
