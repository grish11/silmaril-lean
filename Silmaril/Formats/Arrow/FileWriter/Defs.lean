module

public import Silmaril.Formats.Arrow.FileReader.Defs
public import Silmaril.Formats.Arrow.FooterWriter.Defs
public import Silmaril.Formats.Arrow.StreamWriter.Defs

/-! Checked files for the flat Arrow IPC V5 profile. The stream framing,
schema payload and physical record writer are shared with stream emission. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.FileWriter

structure RecordFrame where
  bytes : KBytes
  metadataLength : Nat
  bodyLength : Nat

def RecordFrame.block (frame : RecordFrame) (offset : Nat) : FileBlock :=
  ⟨offset, frame.metadataLength, frame.bodyLength⟩

def RecordFrame.Fits (frame : RecordFrame) : Prop :=
  frame.bytes.len = frame.metadataLength + frame.bodyLength ∧
    8 ≤ frame.metadataLength ∧ frame.metadataLength % 8 = 0 ∧ frame.bodyLength % 8 = 0

def emitRecord (limits : ObservationLimits) (fields : List Field) (input : Writer.BatchInput) :
    Except Error RecordFrame := do
  if input.fields ≠ fields then throw (.malformed .batchLayout)
  let batch ← Writer.emitBatch limits input
  let message : Message := ⟨.recordBatch batch.metadata, batch.body.len⟩
  let bytes ← StreamWriter.emitFrame limits.ipc message batch.body
  return ⟨bytes, 8 + MetadataWriter.wireSize message, batch.body.len⟩

/-- Assign each wire record its absolute offset, then append modern EOS. -/
def packRecords (offset : Nat) : List RecordFrame → List FileBlock × KBytes
  | [] => ([], StreamWriter.eos)
  | record :: rest =>
    let block := record.block offset
    let (blocks, wire) := packRecords block.endOffset rest
    (block :: blocks, record.bytes ++ wire)

/-- Assembly retains the expected footer and its byte boundaries for the
checked emission step. -/
structure Assembly where
  bytes : KBytes
  footer : FileFooter
  schemaEnd : Nat
  footerStart : Nat
  footerLength : Nat

def assemble (limits : ObservationLimits) (fields : List Field) (inputs : List Writer.BatchInput) :
    Except Error Assembly := do
  if inputs.length > limits.ipc.batches then throw (.limit .batches)
  Body.checkBudget limits fields.length (inputs.map (·.rowCount)).sum
  let schema ← StreamWriter.emitFrame limits.ipc ⟨.schema fields, 0⟩ KBytes.empty
  let records ← inputs.mapM (emitRecord limits fields)
  let schemaEnd := 8 + schema.len
  let (blocks, body) := packRecords schemaEnd records
  let footerStart := schemaEnd + body.len
  let footer : FileFooter := ⟨fields, blocks⟩
  let metadata ← FooterWriter.serialize limits.ipc footer
  let trailer := KBytes.leaf 4 metadata.len ++ KBytes.leaf 6 FileReader.magic
  return ⟨KBytes.leaf 8 FileReader.magic ++ (schema ++ (body ++ (metadata ++ trailer))),
    footer, schemaEnd, footerStart, metadata.len⟩

/-- Confirm that the file reader recovers the exact planned schema and index
from the assembled bytes. Row materialization is kept in FileReader. -/
def emit (limits : ObservationLimits) (fields : List Field) (inputs : List Writer.BatchInput) :
    Except Error KBytes := do
  let plan ← assemble limits fields inputs
  let index ← FileReader.readIndex limits.ipc plan.bytes
  if index.footer = plan.footer ∧ index.schemaEnd = plan.schemaEnd ∧
      index.span.start = plan.footerStart ∧ index.span.length = plan.footerLength then
    return plan.bytes
  else throw (.malformed .batchLayout)

end Silmaril.Formats.Arrow.FileWriter
