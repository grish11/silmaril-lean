module

public import Silmaril.Formats.Arrow.MetadataWriter.Defs

/-! Assemble a finite flat V5 stream from a bodyless schema and checked
physical batches. The stream uses modern continuation words and explicit EOS. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.StreamWriter

/-- Two little-endian words, with the continuation marker first. -/
def envelopeBytes (metadataLength : Nat) : KBytes :=
  KBytes.leaf 4 0xffffffff ++ KBytes.leaf 4 metadataLength

/-- A zero metadata length ends the stream. -/
def eos : KBytes := envelopeBytes 0

def checkBody (limits : Limits) (message : Message) (body : KBytes) : Except Error Unit :=
  if message.bodyLength ≠ body.len || body.len % 8 ≠ 0 then .error (.malformed .bodyLength)
  else if !body.wf then .error (.malformed .source)
  else if body.len > limits.bodyBytes then .error (.limit .bodyBytes)
  else .ok ()

def emitFrame (limits : Limits) (message : Message) (body : KBytes) : Except Error KBytes := do
  checkBody limits message body
  let metadata ← MetadataWriter.emit limits message
  return envelopeBytes metadata.len ++ (metadata ++ body)

def emitRecord (limits : ObservationLimits) (fields : List Field)
    (input : Writer.BatchInput) : Except Error KBytes := do
  if input.fields ≠ fields then throw (.malformed .batchLayout)
  let frame ← Writer.emitBatch limits input
  emitFrame limits.ipc ⟨.recordBatch frame.metadata, frame.body.len⟩ frame.body

/-- Write the schema, each batch in input order, and EOS. A schema can have
no batches, and a zero-column batch retains its explicit row count. -/
def emit (limits : ObservationLimits) (fields : List Field) (batches : List Writer.BatchInput) :
    Except Error KBytes := do
  if batches.length > limits.ipc.batches then throw (.limit .batches)
  Body.checkBudget limits fields.length (batches.map (·.rowCount)).sum
  let schema ← emitFrame limits.ipc ⟨.schema fields, 0⟩ KBytes.empty
  let records ← batches.mapM (emitRecord limits fields)
  return schema ++ records.foldr (· ++ ·) eos

end Silmaril.Formats.Arrow.StreamWriter
