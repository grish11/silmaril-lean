module

public import Silmaril.Formats.Parquet.DeltaLengthByteArray.Defs
import Silmaril.Proofs.Formats.Parquet.DeltaLengthByteArray.Correctness

/-! Exact length-to-value correspondence and full scalar-slice consumption. -/

public section

namespace Silmaril.Formats.Parquet.DeltaLengthByteArray

theorem assemble_ok_iff {limits : Limits} {lengths : List Int32} {payload : List UInt8}
    {values : List Bytes} :
    assemble limits lengths payload = .ok values ↔ Assembled limits lengths payload values :=
  Proofs.Formats.Parquet.DeltaLengthByteArray.assemble_ok_iff

theorem decode_sound {limits : Limits} {expected : Nat} {source : Bytes}
    {values : List Bytes} (h : decode limits expected source = .ok values) :
    ∃ (stream : DeltaBinaryPacked.Stream) (payload : List UInt8),
      source.length ≤ limits.lengths.bytes ∧ source.toList = stream.wire ++ payload ∧
      source.length = stream.wire.length + (values.map Bytes.length).sum ∧
      stream.Valid .int32 limits.lengths expected ∧
      Assembled limits (stream.reconstruct .int32) payload values ∧ values.length = expected :=
  Proofs.Formats.Parquet.DeltaLengthByteArray.decode_sound h

end Silmaril.Formats.Parquet.DeltaLengthByteArray
