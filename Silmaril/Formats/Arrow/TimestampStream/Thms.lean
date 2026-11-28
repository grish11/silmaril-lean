module

public import Silmaril.Formats.Arrow.TimestampStream.Defs
import Silmaril.Proofs.Formats.Arrow.TimestampStream.Framing

public section

namespace Silmaril.Formats.Arrow.TimestampStream

/-- The retained binding is exactly the binding of the first framed Schema. -/
theorem readSchema_iff (limits : Limits) (input : KBytes) (binding : TimestampBatch.Binding)
    (start : Nat) :
    readSchema limits input = .ok (binding, start) ↔
      ∃ size schema,
        readEnvelope limits input 0 = .ok (.metadata size) ∧
        SchemaReader.readMessage limits (input.slice 8 size) = .ok schema ∧
        TimestampBatch.bindSchema schema = .ok binding ∧ start = 8 + size :=
  Proofs.Formats.Arrow.TimestampStream.readSchema_iff limits input binding start

/-- At an admitted metadata span, the record supplies its own checked body,
decoded using the retained binding, and determines the next frame boundary. -/
theorem readBatch_iff (limits : Limits) (input : KBytes) (binding : TimestampBatch.Binding)
    (offset size : Nat) (slots : TimestampBatch.Column binding) (next : Nat) :
    readBatch limits input binding offset size = .ok (slots, next) ↔
      ∃ batch length body,
        Arrow.readMessage limits (input.slice (offset + 8) size) = .ok ⟨.recordBatch batch, length⟩ ∧
        readBody limits input (offset + 8 + size) length = .ok body ∧
        TimestampBatch.decodeBatch limits binding ⟨.recordBatch batch, length⟩ body = .ok slots ∧
        next = offset + 8 + size + length :=
  Proofs.Formats.Arrow.TimestampStream.readBatch_iff limits input binding offset size slots next

/-- The suffix accounts for each record in wire order, within budget, through
EOS at the exact end of the byte carrier. -/
theorem readBatches_iff (limits : Limits) (input : KBytes) (binding : TimestampBatch.Binding)
    (remaining index offset : Nat) (batches : List (TimestampBatch.Column binding)) :
    readBatches limits input binding remaining index offset = .ok batches ↔
      BatchesWire limits input binding remaining offset batches :=
  Proofs.Formats.Arrow.TimestampStream.readBatches_iff limits input binding remaining index offset batches

/-- Complete stream success pairs the first Schema with the ordered record suffix. -/
theorem read_iff (limits : Limits) (input : KBytes) (result : Stream) :
    read limits input = .ok result ↔
      input.wf = true ∧
        ∃ start, readSchema limits input = .ok (result.binding, start) ∧
          BatchesWire limits input result.binding limits.batches start result.batches :=
  Proofs.Formats.Arrow.TimestampStream.read_iff limits input result

end Silmaril.Formats.Arrow.TimestampStream
