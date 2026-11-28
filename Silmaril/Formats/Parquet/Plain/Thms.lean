module

public import Silmaril.Formats.Parquet.Plain.Defs
import Silmaril.Proofs.Formats.Parquet.Plain.Boolean
import Silmaril.Proofs.Formats.Parquet.Plain.FixedWidth
import Silmaril.Proofs.Formats.Parquet.Plain.Signed

/-! Exact consumption for PLAIN readers and round trips on their physical values. -/

public section

namespace Silmaril.Formats.Parquet.Plain

/-- A successful read partitions the entire source into the requested number
of positive-width words and decodes each word in order. -/
theorem decodeFixedWidth_ok_iff {α : Type} {width count : Nat}
    {readWord : List UInt8 → α} {source : Bytes} {values : List α} :
    decodeFixedWidth width count readWord source = .ok values ↔
      0 < width ∧ ∃ words : List (List UInt8),
        source.toList = words.flatten ∧ words.length = count ∧
        (∀ word ∈ words, word.length = width) ∧ values = words.map readWord :=
  Proofs.Formats.Parquet.Plain.decodeFixedWidth_ok_iff

theorem decodeInt32_encodeInt32 (values : List Int32) :
    decodeInt32 values.length (encodeInt32 values) = .ok values :=
  Proofs.Formats.Parquet.Plain.decodeInt32_encodeInt32 values

theorem decodeInt64_encodeInt64 (values : List Int64) :
    decodeInt64 values.length (encodeInt64 values) = .ok values :=
  Proofs.Formats.Parquet.Plain.decodeInt64_encodeInt64 values

/-- The checked unbounded-integer writer admits precisely the signed 32-bit range. -/
theorem encodeInt32Checked_eq (values : List Int) :
    encodeInt32Checked values =
      if ∀ value ∈ values, -(2 ^ 31 : Int) ≤ value ∧ value < 2 ^ 31 then
        .ok (encodeInt32 (values.map Int32.ofInt))
      else .error .integerOverflow :=
  Proofs.Formats.Parquet.Plain.encodeInt32Checked_eq values

/-- The checked unbounded-integer writer admits precisely the signed 64-bit range. -/
theorem encodeInt64Checked_eq (values : List Int) :
    encodeInt64Checked values =
      if ∀ value ∈ values, -(2 ^ 63 : Int) ≤ value ∧ value < 2 ^ 63 then
        .ok (encodeInt64 (values.map Int64.ofInt))
      else .error .integerOverflow :=
  Proofs.Formats.Parquet.Plain.encodeInt64Checked_eq values

theorem decodeFloatBits_encodeFloatBits (values : List UInt32) :
    decodeFloatBits values.length (encodeFloatBits values) = .ok values :=
  Proofs.Formats.Parquet.Plain.decodeFloatBits_encodeFloatBits values

theorem decodeDoubleBits_encodeDoubleBits (values : List UInt64) :
    decodeDoubleBits values.length (encodeDoubleBits values) = .ok values :=
  Proofs.Formats.Parquet.Plain.decodeDoubleBits_encodeDoubleBits values

theorem decodeFixedLenBytes_encodeFixedLenBytes {width : Nat} {values : List Bytes}
    {source : Bytes} (encoded : encodeFixedLenBytes width values = .ok source) :
    decodeFixedLenBytes width values.length source = .ok values :=
  Proofs.Formats.Parquet.Plain.decodeFixedLenBytes_encodeFixedLenBytes encoded

/-- An accepted Boolean source has exactly enough bytes, and value `i` is
bit `i % 8` of byte `i / 8`. -/
theorem decodeBoolean_ok_iff {count : Nat} {source : Bytes} {values : List Bool} :
    decodeBoolean count source = .ok values ↔
      source.length = booleanByteCount count ∧ values.length = count ∧
        ∀ i : Nat, (hi : i < values.length) →
          (source.toList[i / 8]?).map (fun byte => byte.toNat.testBit (i % 8)) = some values[i] :=
  Proofs.Formats.Parquet.Plain.decodeBoolean_ok_iff

theorem encodeBoolean_length (values : List Bool) :
    (encodeBoolean values).length = booleanByteCount values.length :=
  Proofs.Formats.Parquet.Plain.encodeBoolean_length values

/-- The writer sets each used bit to its Boolean value and each padding bit to zero. -/
theorem encodeBoolean_bit (values : List Bool) {octet bit : Nat}
    (ho : octet < booleanByteCount values.length) (hb : bit < 8) :
    ((encodeBoolean values).toList[octet]?).map (fun byte => byte.toNat.testBit bit) =
      some (values[8 * octet + bit]?.getD false) :=
  Proofs.Formats.Parquet.Plain.encodeBoolean_bit values ho hb

theorem decodeBoolean_encodeBoolean (values : List Bool) :
    decodeBoolean values.length (encodeBoolean values) = .ok values :=
  Proofs.Formats.Parquet.Plain.decodeBoolean_encodeBoolean values

end Silmaril.Formats.Parquet.Plain
