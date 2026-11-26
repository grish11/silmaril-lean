module

public import Silmaril.Formats.Parquet.ByteStreamSplit.Defs
import Silmaril.Proofs.Formats.Parquet.ByteStreamSplit.Correctness

/-! Exact extent and indexed lane order for bounded BYTE_STREAM_SPLIT. -/

public section

namespace Silmaril.Formats.Parquet.ByteStreamSplit

/-- Successful transposition implements exactly the admitted lane layout. -/
theorem decodeWords_ok_iff {limits : Limits} {width count : Nat} {source : Bytes}
    {words : List (List UInt8)} :
    decodeWords limits width count source = .ok words ↔
      Admission limits width count source ∧ LaneOrder width count source words :=
  Proofs.Formats.Parquet.ByteStreamSplit.decodeWords_ok_iff

/-- The typed result uses the transposed words in the same order. -/
theorem decode_sound {kind : Kind} {limits : Limits} {count : Nat} {source : Bytes}
    {values : List kind.Value} (h : decode kind limits count source = .ok values) :
    ∃ words, Admission limits kind.width count source ∧ LaneOrder kind.width count source words ∧
      values = words.map kind.readWord ∧ values.length = count :=
  Proofs.Formats.Parquet.ByteStreamSplit.decode_sound h

end Silmaril.Formats.Parquet.ByteStreamSplit
