module

public import Silmaril.Formats.Parquet.ScalarPage.BrotliRaw.Defs
import Silmaril.Proofs.Formats.Parquet.ScalarPage.BrotliRaw.Contracts

public section

namespace Silmaril.Formats.Parquet.ScalarPage.BrotliRaw

open Silmaril.Formats.Compression

/-- An accepted payload consumes the exact original slice and meets the declared
expanded length and caller limits. -/
theorem decodePayload_sound {limits : Limits} {bounds : Payload.Bounds} {input output : List UInt8}
    (read : decodePayload limits bounds input = .ok output) : PayloadWire limits bounds input output :=
  Proofs.Formats.Parquet.ScalarPage.BrotliRaw.decodePayload_sound read

/-- Once the external extent checks pass, stream failures retain their cause,
with an overrun of the declared plain length reported as a size mismatch. -/
theorem decodePayload_streamError {limits : Limits} {bounds : Payload.Bounds}
    {input : List UInt8} {error : Brotli.Error}
    (inputFits : bounds.compressedSize ≤ bounds.compressedLimit)
    (outputFits : bounds.expectedSize ≤ bounds.outputLimit) (extent : input.length = bounds.compressedSize)
    (read : Brotli.decode (streamLimits limits bounds) input = .error error) :
    decodePayload limits bounds input = .error (streamError error) :=
  Proofs.Formats.Parquet.ScalarPage.BrotliRaw.decodePayload_streamError inputFits outputFits extent read

/-- Successful V1 expansion covers the entire original body. V2 keeps the
exact raw level prefix and resolves the flag on the exact value suffix. -/
theorem decodePage_sound {limits : Limits} {pageLimits : ScalarPage.Limits}
    {params : ScalarPage.Parameters} {source : Bytes} {output : List UInt8}
    (read : decodePage limits pageLimits params source = .ok output) :
    PageWire limits pageLimits params source output :=
  Proofs.Formats.Parquet.ScalarPage.BrotliRaw.decodePage_sound read

end Silmaril.Formats.Parquet.ScalarPage.BrotliRaw
