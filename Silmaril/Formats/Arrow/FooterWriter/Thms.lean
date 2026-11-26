module

public import Silmaril.Formats.Arrow.FooterWriter.Defs
import Silmaril.Proofs.Formats.Arrow.FooterWriter

@[expose] public section

namespace Silmaril.Formats.Arrow.FooterWriter

/-- The encoder's exact footer length fits the signed trailer and the
configured metadata budget. -/
theorem serialize_extent {limits : Limits} {footer : FileFooter} {bytes : KBytes}
    (written : serialize limits footer = .ok bytes) :
    bytes.wf = true ∧ bytes.len = wireSize footer ∧ 0 < bytes.len ∧
      bytes.len % 8 = 0 ∧ bytes.len < 2^31 ∧ bytes.len ≤ limits.metadataBytes :=
  Proofs.Formats.Arrow.FooterWriter.serialize_extent written

/-- A checked footer write recovers the exact schema and ordered blocks. -/
theorem emit_exact {limits : Limits} {footer : FileFooter} {bytes : KBytes}
    (written : emit limits footer = .ok bytes) :
    serialize limits footer = .ok bytes ∧
      readFileFooter limits (bytes.slice 0 bytes.len) = .ok footer :=
  Proofs.Formats.Arrow.FooterWriter.emit_exact written

end Silmaril.Formats.Arrow.FooterWriter
