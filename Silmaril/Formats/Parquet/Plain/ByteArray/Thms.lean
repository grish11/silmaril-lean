module

public import Silmaril.Formats.Parquet.Plain.ByteArray.Defs
import Silmaril.Proofs.Formats.Parquet.Plain.ByteArray.Wire

/-! Exact bounded wire acceptance and a general checked-writer round trip. -/

public section

namespace Silmaril.Formats.Parquet.Plain.ByteArray

theorem decode_ok_iff {limits : Limits} {count : Nat} {source : Bytes} {values : List Bytes} :
    decode limits count source = .ok values ↔
      source.length ≤ limits.totalBytes ∧ source.toList = wire values ∧ values.length = count ∧
      ∀ value ∈ values, value.length < lengthLimit ∧ value.length ≤ limits.valueBytes :=
  Proofs.Formats.Parquet.Plain.ByteArray.decode_ok_iff

theorem encode_ok_iff {limits : Limits} {values : List Bytes} {source : Bytes} :
    encode limits values = .ok source ↔
      encodedSize values ≤ limits.totalBytes ∧ source.toList = wire values ∧
      ∀ value ∈ values, value.length < lengthLimit ∧ value.length ≤ limits.valueBytes :=
  Proofs.Formats.Parquet.Plain.ByteArray.encode_ok_iff

theorem decode_size {limits : Limits} {count : Nat} {source : Bytes} {values : List Bytes}
    (h : decode limits count source = .ok values) : source.length = encodedSize values :=
  Proofs.Formats.Parquet.Plain.ByteArray.decode_size h

theorem decode_encode {limits : Limits} {values : List Bytes} {source : Bytes}
    (h : encode limits values = .ok source) : decode limits values.length source = .ok values :=
  Proofs.Formats.Parquet.Plain.ByteArray.decode_encode h

theorem encode_size {limits : Limits} {values : List Bytes} {source : Bytes}
    (h : encode limits values = .ok source) : source.length = encodedSize values :=
  decode_size (decode_encode h)

theorem encode_decode {limits : Limits} {count : Nat} {source : Bytes} {values : List Bytes}
    (h : decode limits count source = .ok values) : encode limits values = .ok source :=
  Proofs.Formats.Parquet.Plain.ByteArray.encode_decode h

end Silmaril.Formats.Parquet.Plain.ByteArray
