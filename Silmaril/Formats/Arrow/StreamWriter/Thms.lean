module

public import Silmaril.Formats.Arrow.StreamWriter.Defs
public import Silmaril.Formats.Arrow.StreamWriter.Window.Defs
import Silmaril.Proofs.Formats.Arrow.StreamWriter.Framing
import Silmaril.Proofs.Formats.Arrow.StreamWriter.RoundTrip

@[expose] public section

namespace Silmaril.Formats.Arrow.StreamWriter

theorem read_eos (limits : Limits) : readEnvelope limits eos 0 = .ok .eos :=
  Proofs.Formats.Arrow.StreamWriter.read_eos limits

/-- The existing framing and metadata readers recover the exact message and
body byte window from every emitted frame. -/
theorem emitFrame_exact {limits : Limits} {message : Message} {body wire : KBytes}
    (written : emitFrame limits message body = .ok wire) :
    let size := MetadataWriter.wireSize message
    wire.wf = true ∧ wire.len = 8 + size + message.bodyLength ∧
      readEnvelope limits wire 0 = .ok (.metadata size) ∧
      readMessage limits (wire.slice 8 size) = .ok message ∧
      ∃ extracted, readBody limits wire (8 + size) message.bodyLength = .ok extracted ∧
        extracted.toList = body.toList :=
  Proofs.Formats.Arrow.StreamWriter.emitFrame_exact written

/-- Read a framed physical batch at its position in an enclosing carrier. -/
theorem emitBatchFrame_at {limits : ObservationLimits}
    {input : Writer.BatchInput} {physical : BatchFrame input.fields}
    {part whole : KBytes} {start : Nat}
    (written : Writer.emitBatch limits input = .ok physical)
    (framed : emitFrame limits.ipc ⟨.recordBatch physical.metadata, physical.body.len⟩
      physical.body = .ok part)
    (atRecord : Window part whole start) (aligned : start % 8 = 0) :
    let size := MetadataWriter.wireSize ⟨.recordBatch physical.metadata, physical.body.len⟩
    ∃ (raw : KBytes) (batch : BatchFrame input.fields),
      part.wf = true ∧ part.len = 8 + size + physical.body.len ∧ part.len % 8 = 0 ∧
      readEnvelope limits.ipc whole start = .ok (.metadata size) ∧
      readMessage limits.ipc (whole.slice (start + 8) size) =
        .ok ⟨.recordBatch batch.metadata, physical.body.len⟩ ∧
      readBody limits.ipc whole (start + 8 + size) physical.body.len = .ok raw ∧
      validateBatch input.fields batch.metadata raw = .ok batch ∧
      batch.metadata.rowCount = input.rowCount ∧
      decodeBatch limits batch = .ok input.observe ∧ input.observe.length = input.rowCount :=
  Proofs.Formats.Arrow.StreamWriter.emitBatchFrame_at written framed atRecord aligned

/-- Every successful emission is readable under the same limits. The declared
schema, batch order, explicit metadata counts, and ordered nullable rows are
preserved. Each observed batch has its declared row count even at zero columns. -/
theorem emit_roundtrip {limits : ObservationLimits} {fields : List Field}
    {inputs : List Writer.BatchInput} {wire : KBytes} (written : emit limits fields inputs = .ok wire) :
    ∃ stream : Stream, readStream limits.ipc wire = .ok stream ∧ stream.fields = fields ∧
      stream.batches.map (·.metadata.rowCount) = inputs.map (·.rowCount) ∧
      readRows limits wire = .ok ⟨fields, inputs.map Writer.BatchInput.observe⟩ ∧
      (inputs.map Writer.BatchInput.observe).map List.length = inputs.map (·.rowCount) :=
  Proofs.Formats.Arrow.StreamWriter.emit_roundtrip written

/-- A read returns one ordered nullable observation per emitted batch. -/
theorem emit_readRows {limits : ObservationLimits} {fields : List Field}
    {inputs : List Writer.BatchInput} {wire : KBytes} (written : emit limits fields inputs = .ok wire) :
    readRows limits wire = .ok ⟨fields, inputs.map Writer.BatchInput.observe⟩ := by
  obtain ⟨_, _, _, _, observed, _⟩ := emit_roundtrip written
  exact observed

end Silmaril.Formats.Arrow.StreamWriter
