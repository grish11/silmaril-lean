module

public import Silmaril.Formats.Parquet.DeltaByteArray.Defs
import Silmaril.Proofs.Formats.Parquet.DeltaByteArray.Correctness

/-! Exact encoding-7 extent and ordered reconstruction from the preceding value. -/

public section

namespace Silmaril.Formats.Parquet.DeltaByteArray

theorem reconstruct_ok_iff {limits : Limits} {prefixes : List Int32} {suffixes values : List Bytes} :
    reconstruct limits prefixes suffixes = .ok values ↔ prefixes.headD 0 = 0 ∧
      Reconstruction limits.valueBytes limits.decodedBytes .empty prefixes suffixes values :=
  Proofs.Formats.Parquet.DeltaByteArray.reconstruct_ok_iff

theorem reconstruction_sizes {limit budget : Nat} {previous : Bytes}
    {prefixes : List Int32} {suffixes values : List Bytes}
    (h : Reconstruction limit budget previous prefixes suffixes values) :
    values.length = prefixes.length ∧ values.length = suffixes.length ∧
      (values.map Bytes.length).sum ≤ budget :=
  Proofs.Formats.Parquet.DeltaByteArray.reconstruction_sizes h

theorem decode_sound {limits : Limits} {expected : Nat} {source : Bytes}
    {values : List Bytes} (h : decode limits expected source = .ok values) :
    ∃ (prefixStream suffixStream : DeltaBinaryPacked.Stream) (payload : List UInt8)
        (suffixes : List Bytes),
      source.length ≤ limits.prefixes.bytes ∧
      source.toList = prefixStream.wire ++ suffixStream.wire ++ payload ∧
      source.length = prefixStream.wire.length + suffixStream.wire.length + (suffixes.map Bytes.length).sum ∧
      prefixStream.Valid .int32 limits.prefixes expected ∧
      suffixStream.Valid .int32 limits.suffixes.lengths expected ∧
      DeltaLengthByteArray.Assembled limits.suffixes (suffixStream.reconstruct .int32) payload suffixes ∧
      (prefixStream.reconstruct .int32).headD 0 = 0 ∧
      Reconstruction limits.valueBytes limits.decodedBytes .empty
        (prefixStream.reconstruct .int32) suffixes values ∧
      values.length = expected ∧ (values.map Bytes.length).sum ≤ limits.decodedBytes :=
  Proofs.Formats.Parquet.DeltaByteArray.decode_sound h

end Silmaril.Formats.Parquet.DeltaByteArray
