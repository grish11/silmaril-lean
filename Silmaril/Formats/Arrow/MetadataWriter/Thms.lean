module

public import Silmaril.Formats.Arrow.MetadataWriter.Defs
import Silmaril.Proofs.Formats.Arrow.MetadataWriter.Size

@[expose] public section

namespace Silmaril.Formats.Arrow.MetadataWriter

theorem wireSize_aligned (message : Message) : 0 < wireSize message ∧ wireSize message % 8 = 0 :=
  Proofs.Formats.Arrow.MetadataWriter.wireSize_aligned message

/-- Serialization computes the exact padded extent within the signed
framing range and the configured metadata budget. -/
theorem serialize_extent {limits : Limits} {message : Message} {bytes : KBytes}
    (written : serialize limits message = .ok bytes) :
    bytes.wf = true ∧ bytes.len = wireSize message ∧ bytes.len < 2^31 ∧
      bytes.len ≤ limits.metadataBytes :=
  Proofs.Formats.Arrow.MetadataWriter.serialize_extent written

/-- A successful write recovers the original message from its whole metadata
window. This includes the body length and explicit row count. -/
theorem emit_exact {limits : Limits} {message : Message} {bytes : KBytes}
    (written : emit limits message = .ok bytes) :
    readMessage limits (bytes.slice 0 bytes.len) = .ok message ∧ bytes.wf = true ∧
      bytes.len = wireSize message ∧ 0 < bytes.len ∧ bytes.len < 2^31 ∧
      bytes.len % 8 = 0 ∧ bytes.len ≤ limits.metadataBytes :=
  Proofs.Formats.Arrow.MetadataWriter.emit_exact written

end Silmaril.Formats.Arrow.MetadataWriter
