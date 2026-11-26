module

public import Silmaril.Formats.Arrow.StreamWriter.Defs
import Silmaril.Proofs.Formats.Arrow.StreamWriter.Framing

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

end Silmaril.Formats.Arrow.StreamWriter
