module

public import Silmaril.Formats.Arrow.DateBatch.Defs
import Silmaril.Proofs.Formats.Arrow.DateBatch.Binding

public section

namespace Silmaril.Formats.Arrow.DateBatch

/-- Successful decoding is exactly the sole normalized DATE field, the
corresponding record metadata and body extent, and the ordered nullable
observation of the checked body buffers. -/
theorem decode_iff (limits : Limits) (schemaMetadata recordMetadata body : KBytes)
    (dates : DateValues.Column) :
    decode limits schemaMetadata recordMetadata body = .ok dates ↔
      ∃ endian name nullable unit batch view,
        SchemaReader.readMessage limits schemaMetadata =
          .ok ⟨endian, [⟨name, nullable, .date unit⟩]⟩ ∧
        Arrow.readMessage limits recordMetadata = .ok ⟨.recordBatch batch, body.len⟩ ∧
        body.len % 8 = 0 ∧
        DateValues.batchView limits batch body = .ok view ∧
        DateValues.check limits (dateDecoder unit) (descriptor endian unit nullable) view = .ok () ∧
        DateValues.ColumnWire (dateDecoder unit) view dates :=
  Proofs.Formats.Arrow.DateBatch.decode_iff limits schemaMetadata recordMetadata body dates

/-- The result has exactly the declared rows and field-node null count. -/
theorem decode_counts {limits : Limits} {schemaMetadata recordMetadata body : KBytes}
    {dates : DateValues.Column} (decoded : decode limits schemaMetadata recordMetadata body = .ok dates) :
    ∃ batch node, Arrow.readMessage limits recordMetadata = .ok ⟨.recordBatch batch, body.len⟩ ∧
      batch.nodes = [node] ∧ dates.length = batch.rowCount ∧
      dates.countP Option.isNone = node.nullCount :=
  Proofs.Formats.Arrow.DateBatch.decode_counts decoded

end Silmaril.Formats.Arrow.DateBatch
