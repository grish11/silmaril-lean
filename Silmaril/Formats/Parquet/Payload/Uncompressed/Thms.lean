module

public import Silmaril.Formats.Parquet.Payload.Defs
import Silmaril.Proofs.Formats.Parquet.Payload.Uncompressed

/-! The identity law for the bounded UNCOMPRESSED payload. -/

public section

namespace Silmaril.Formats.Parquet.Payload

theorem decode_uncompressed {bounds : Bounds} {input : List UInt8}
    (compressed : bounds.compressedSize ≤ bounds.compressedLimit)
    (output : bounds.expectedSize ≤ bounds.outputLimit)
    (stored : input.length = bounds.compressedSize) (expanded : input.length = bounds.expectedSize) :
    decode bounds Codec.uncompressed.id input = .ok input :=
  Proofs.Formats.Parquet.Payload.decode_uncompressed compressed output stored expanded

end Silmaril.Formats.Parquet.Payload
