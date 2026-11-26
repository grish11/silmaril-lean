module

public import Silmaril.Formats.Parquet.Payload.Defs

public section

namespace Silmaril.Proofs.Formats.Parquet.Payload

open Silmaril.Formats.Parquet.Payload

private theorem hasLength_self (input : List UInt8) : Internal.hasLength input.length input = true := by
  induction input <;> simp_all [Internal.hasLength]

theorem decode_uncompressed {bounds : Bounds} {input : List UInt8}
    (compressed : bounds.compressedSize ≤ bounds.compressedLimit)
    (output : bounds.expectedSize ≤ bounds.outputLimit)
    (stored : input.length = bounds.compressedSize) (expanded : input.length = bounds.expectedSize) :
    decode bounds Codec.uncompressed.id input = .ok input := by
  have extent : Internal.hasLength bounds.compressedSize input = true := by
    rw [← stored]
    exact hasLength_self input
  simp [decode, Nat.not_lt.mpr compressed, Nat.not_lt.mpr output, extent,
    Codec.id, Codec.ofId, Internal.decodeCodec, expanded, Bind.bind, Except.bind]

end Silmaril.Proofs.Formats.Parquet.Payload
