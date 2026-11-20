module

public import Silmaril.Formats.Cbor.Drisl.Number.Defs

@[expose] public section

namespace Silmaril.Proofs.Formats.Cbor.Drisl.Number

open Silmaril.Formats.Cbor.Drisl

theorem exactInt_intDecimal (value : Int) : exactInt? (intDecimal value) = some value := by
  cases value with
  | ofNat amount =>
    cases amount <;> simp [exactInt?, intDecimal, Silmaril.Formats.JsonWire.Decimal.toInt?]
  | negSucc amount =>
    simp [exactInt?, intDecimal, Silmaril.Formats.JsonWire.Decimal.toInt?, Int.negSucc_eq]

theorem int64_toInt (value : Int64) : int64? value.toInt = some value := by
  rw [int64?, ite_eq_left ⟨value.le_toInt, value.toInt_lt⟩, Int64.ofInt_toInt]

theorem ofInt_toInt (value : Integer) : Integer.ofInt? value.toInt = some value := by
  cases value with
  | uint argument =>
    have bound : argument.toNat < 18446744073709551616 := argument.toNat_lt
    simp [Integer.ofInt?, Integer.toInt, bound]
  | nint argument =>
    have bound : argument.toNat < 18446744073709551616 := argument.toNat_lt
    simp [Integer.ofInt?, Integer.toInt, bound]

theorem toInt_ofInt64 (value : Int64) : (Integer.ofInt64 value).toInt = value.toInt := by
  have lower := value.le_toInt
  unfold Integer.ofInt64
  cases intEq : value.toInt with
  | ofNat amount =>
    have upper := value.toNatClampNeg_lt
    rw [← Int64.toNat_toInt, intEq] at upper
    have small : amount < 2 ^ 63 := upper
    have bound : amount < 18446744073709551616 := by omega
    simp [Integer.toInt, UInt64.toNat_ofNat', Nat.mod_eq_of_lt bound]
  | negSucc amount =>
    have bound : amount < 18446744073709551616 := by omega
    simp [Integer.toInt, UInt64.toNat_ofNat', Nat.mod_eq_of_lt bound]

theorem exponent_lt (bits : Float64Bits) : floatExponent bits.val < 2047 := by
  have bound := Nat.mod_lt (bits.val / 2 ^ 52) (by decide : 0 < 2048)
  have valid := bits.property
  simp only [okFloat64, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at valid
  unfold floatExponent
  have notMax := valid.1.2
  change bits.val / 2 ^ 52 % 2048 ≠ 2047 at notMax
  omega

theorem join_bits (bits : Float64Bits) :
    (if 2 ^ 63 ≤ bits.val then 2 ^ 63 else 0) + floatExponent bits.val * 2 ^ 52 +
      bits.val % 2 ^ 52 = bits.val := by
  have valid := bits.property
  simp only [okFloat64, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at valid
  have bound : bits.val < 18446744073709551616 := valid.1.1
  change (if 9223372036854775808 ≤ bits.val then 9223372036854775808 else 0) +
    bits.val / 4503599627370496 % 2048 * 4503599627370496 + bits.val % 4503599627370496 = bits.val
  split <;> omega

theorem float_inverse (bits : Float64Bits) : readFloatDecimal? (floatDecimal bits) = some bits := by
  have expBound := exponent_lt bits
  generalize expEq : floatExponent bits.val = exp at *
  have exponentBack : (2047 + -(2047 - (exp : Int))).toNat = exp := by omega
  have exponentRange : -(2047 : Int) ≤ -(2047 - (exp : Int)) ∧ -(2047 - (exp : Int)) ≤ -1 := by omega
  have factorPos : 0 < floatScaleFactor exp :=
    Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide))
  have fracBound := Nat.mod_lt bits.val (by decide : 0 < 2 ^ 52)
  simp only [readFloatDecimal?, floatDecimal, expEq, exponentRange, and_self, not_true_eq_false,
    ↓reduceIte, exponentBack, Nat.mul_mod_left, ne_eq,
    Nat.mul_div_cancel _ factorPos]
  have fractionBack : (if exp = 0 then (if exp = 0 then bits.val % 2 ^ 52
      else 2 ^ 52 + bits.val % 2 ^ 52) else
        (if exp = 0 then bits.val % 2 ^ 52 else 2 ^ 52 + bits.val % 2 ^ 52) - 2 ^ 52) =
      bits.val % 2 ^ 52 := by split <;> simp_all
  have sigBound : (if exp = 0 then (if exp = 0 then bits.val % 2 ^ 52 else 2 ^ 52 + bits.val % 2 ^ 52) < 2 ^ 52
      else 2 ^ 52 ≤ (if exp = 0 then bits.val % 2 ^ 52 else 2 ^ 52 + bits.val % 2 ^ 52) ∧
        (if exp = 0 then bits.val % 2 ^ 52 else 2 ^ 52 + bits.val % 2 ^ 52) < 2 ^ 53) := by
    split
    · simp_all
    · simp_all
      omega
  simp only [sigBound, not_true_eq_false, ↓reduceIte, fractionBack]
  have joined := join_bits bits
  rw [expEq] at joined
  simp only [decide_eq_true_eq, joined, bits.property, ↓reduceDIte]

theorem number_inverse (value : Number) : Number.readDecimal? value.toDecimal = some value := by
  cases value with
  | integer integral =>
    have expZero : (intDecimal integral.toInt).exponent = 0 := by
      cases integral <;> rfl
    simp [Number.readDecimal?, Number.toDecimal, expZero, exactInt_intDecimal, ofInt_toInt]
  | float bits =>
    have nonzero : (floatDecimal bits).exponent ≠ 0 := by
      have := exponent_lt bits
      change -(2047 - (floatExponent bits.val : Int)) ≠ 0
      omega
    simp [Number.readDecimal?, Number.toDecimal, nonzero, float_inverse]

end Silmaril.Proofs.Formats.Cbor.Drisl.Number
