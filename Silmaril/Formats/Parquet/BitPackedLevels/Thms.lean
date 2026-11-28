module

public import Silmaril.Formats.Parquet.BitPackedLevels.Defs
import Silmaril.Proofs.Formats.Parquet.BitPackedLevels.Correctness

/-! Exact extent, ordered MSB-first bits, and checked definition/repetition levels. -/

public section

namespace Silmaril.Formats.Parquet.BitPackedLevels

/-- An accepted slice has the exact count-derived prefix, unchanged suffix,
ordered MSB-first levels, and caller and schema bounds. -/
theorem readPrefix_ok_iff {maxLevel count : Nat} {limits : Limits}
    {source rest : Bytes} {levels : List Nat} :
    readPrefix maxLevel count limits source = .ok (levels, rest) ↔
      maxLevel < signedLimit ∧ count < signedLimit ∧ count ≤ limits.levels ∧
      byteCount maxLevel count ≤ limits.bytes ∧
      ∃ packed, source = packed.append rest ∧ Wire maxLevel count packed levels :=
  Proofs.Formats.Parquet.BitPackedLevels.readPrefix_ok_iff

theorem wireCode_testBit (packed : Bytes) (start width j : Nat) (within : j < width) :
    (wireCode packed start width).testBit (width - 1 - j) =
      decide (wireBit packed (start + j) = 1) :=
  Proofs.Formats.Parquet.BitPackedLevels.wireCode_testBit packed start width j within

/-- Relate a bit in a decoded level to its actual position in the packed prefix. -/
theorem Wire.getElem_testBit {maxLevel count : Nat} {packed : Bytes} {levels : List Nat}
    (wire : Wire maxLevel count packed levels) {i j : Nat} (hi : i < levels.length)
    (hj : j < bitWidth maxLevel) :
    levels[i].testBit (bitWidth maxLevel - 1 - j) =
      decide (wireBit packed (i * bitWidth maxLevel + j) = 1) := by
  rw [wire.order i hi]
  exact wireCode_testBit packed _ _ j hj

/-- Every requested field bit addresses an in-bounds prefix byte. -/
theorem position_in_extent {maxLevel count : Nat} {packed : Bytes} {levels : List Nat}
    (wire : Wire maxLevel count packed levels) {i j : Nat} (hi : i < count)
    (hj : j < bitWidth maxLevel) : (i * bitWidth maxLevel + j) / 8 < packed.length :=
  Proofs.Formats.Parquet.BitPackedLevels.position_in_extent wire hi hj

/-- Maximum level zero yields exactly the requested zeros and consumes no bytes. -/
theorem readPrefix_zero {count : Nat} {limits : Limits} {source : Bytes}
    (countFits : count < signedLimit) (cap : count ≤ limits.levels) :
    readPrefix 0 count limits source = .ok (List.replicate count 0, source) :=
  Proofs.Formats.Parquet.BitPackedLevels.readPrefix_zero countFits cap

theorem readExact_ok_iff {maxLevel count : Nat} {limits : Limits}
    {source : Bytes} {levels : List Nat} :
    readExact maxLevel count limits source = .ok levels ↔
      readPrefix maxLevel count limits source = .ok (levels, .empty) :=
  Proofs.Formats.Parquet.BitPackedLevels.readExact_ok_iff

end Silmaril.Formats.Parquet.BitPackedLevels
