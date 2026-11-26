module

public import Silmaril.Formats.Arrow.DateStream.Defs
import Silmaril.Proofs.Formats.Arrow.DateStream.Framing

public section

namespace Silmaril.Formats.Arrow.DateStream

/-- The retained field is exactly the sole normalized little-endian DATE
field in the first framed Schema message. -/
theorem readSchema_iff (limits : Limits) (input : KBytes) (field : Field) (start : Nat) :
    readSchema limits input = .ok (field, start) ↔
      ∃ size,
        readEnvelope limits input 0 = .ok (.metadata size) ∧ start = 8 + size ∧
        SchemaReader.readMessage limits (input.slice 8 size) =
          .ok ⟨.little, [⟨field.name, field.nullable, .date field.unit⟩]⟩ :=
  Proofs.Formats.Arrow.DateStream.readSchema_iff limits input field start

/-- At a known framed metadata span, the record declares its own checked body
slice and next frame boundary. Decoding observes the ordered nullable slots. -/
theorem readBatch_iff (limits : Limits) (input : KBytes) (field : Field)
    (offset size : Nat) (dates : DateValues.Column) (next : Nat) :
    readBatch limits input field offset size = .ok (dates, next) ↔
      ∃ batch length body view,
        Arrow.readMessage limits (input.slice (offset + 8) size) = .ok ⟨.recordBatch batch, length⟩ ∧
        readBody limits input (offset + 8 + size) length = .ok body ∧
        next = offset + 8 + size + length ∧
        DateValues.batchView limits batch body = .ok view ∧
        DateValues.check limits field.decoder field.descriptor view = .ok () ∧
        DateValues.ColumnWire field.decoder view dates :=
  Proofs.Formats.Arrow.DateStream.readBatch_iff limits input field offset size dates next

/-- Success lists every admitted batch in frame order through exact EOS. -/
theorem readBatches_iff (limits : Limits) (input : KBytes) (field : Field)
    (remaining index offset : Nat) (batches : List DateValues.Column) :
    readBatches limits input field remaining index offset = .ok batches ↔
      BatchesWire limits input field remaining offset batches :=
  Proofs.Formats.Arrow.DateStream.readBatches_iff limits input field remaining index offset batches

/-- Batch errors carry precisely the stage and index reached after the
successfully decoded prefix. -/
theorem readBatches_error_iff (limits : Limits) (input : KBytes) (field : Field)
    (remaining index offset failed : Nat) (cause : BatchError) :
    readBatches limits input field remaining index offset = .error (.batch failed cause) ↔
      BatchFailure limits input field remaining index offset failed cause :=
  Proofs.Formats.Arrow.DateStream.readBatches_error_iff limits input field remaining index offset failed cause

/-- A complete stream has one checked Schema followed by its ordered DATE batches. -/
theorem read_iff (limits : Limits) (input : KBytes) (result : Stream) :
    read limits input = .ok result ↔
      input.wf = true ∧
        ∃ start, readSchema limits input = .ok (result.field, start) ∧
          BatchesWire limits input result.field limits.batches start result.batches :=
  Proofs.Formats.Arrow.DateStream.read_iff limits input result

/-- After Schema admission, a stream error identifies the first failed stage
after its preceding decoded batches. -/
theorem read_batch_error_iff {limits : Limits} {input : KBytes} {field : Field}
    {start : Nat} (wellFormed : input.wf = true)
    (schema : readSchema limits input = .ok (field, start)) (failed : Nat) (cause : BatchError) :
    read limits input = .error (.batch failed cause) ↔
      BatchFailure limits input field limits.batches 0 start failed cause :=
  Proofs.Formats.Arrow.DateStream.read_batch_error_iff wellFormed schema failed cause

end Silmaril.Formats.Arrow.DateStream
