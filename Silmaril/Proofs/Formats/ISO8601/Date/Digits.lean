module

public import Silmaril.Formats.ISO8601.Date.Defs

public section

namespace Silmaril.Proofs.Formats.ISO8601.Date

open Silmaril.Formats.ISO8601.Internal (fixedDigits parseFixed?)
open Silmaril.Numeric.DecimalText (digitsValue parseNat)

@[simp] theorem fixedDigits_length (width value : Nat) : (fixedDigits width value).length = width := by
  induction width generalizing value with
  | zero => rfl
  | succ width ih => simp [fixedDigits, ih]

private theorem digitsValue_cons (c : Char) (tail : List Char) :
    digitsValue (c :: tail) = 10 ^ tail.length * (c.toNat - 48) + digitsValue tail := by
  simp only [digitsValue, Nat.ofDigitChars_cons, Nat.mul_zero, Nat.zero_add]
  exact Nat.ofDigitChars_eq_ofDigitChars_zero

private theorem fixedDigits_properties (width value : Nat) (bound : value < 10 ^ width) :
    (fixedDigits width value).all Char.isDigit = true ∧ digitsValue (fixedDigits width value) = value := by
  induction width generalizing value with
  | zero =>
    have : value = 0 := by simpa using bound
    simp [fixedDigits, digitsValue, this]
  | succ width ih =>
    have positive : 0 < (10 : Nat) ^ width := Nat.pow_pos (by decide)
    have quotient : value / 10 ^ width < 10 := by
      exact (Nat.div_lt_iff_lt_mul positive).mpr (by simpa [Nat.pow_succ, Nat.mul_comm] using bound)
    obtain ⟨digitTail, valueTail⟩ := ih (value % 10 ^ width) (Nat.mod_lt _ positive)
    constructor
    · simp [fixedDigits, Nat.isDigit_digitChar, quotient, digitTail]
    · rw [fixedDigits, digitsValue_cons, fixedDigits_length,
        Nat.toNat_digitChar_sub_48_of_lt_ten quotient, valueTail, Nat.div_add_mod]

theorem parseFixed_fixedDigits {width value : Nat} (positive : 0 < width) (bound : value < 10 ^ width) :
    parseFixed? width (fixedDigits width value) = some value := by
  obtain ⟨digits, number⟩ := fixedDigits_properties width value bound
  have nonempty : fixedDigits width value ≠ [] := by
    intro empty
    have length := fixedDigits_length width value
    simp [empty] at length
    omega
  simp [parseFixed?, parseNat, digits, number, nonempty]

private theorem digits_bound_and_render {digits : List Char} (valid : digits.all Char.isDigit = true) :
    digitsValue digits < 10 ^ digits.length ∧ fixedDigits digits.length (digitsValue digits) = digits := by
  induction digits with
  | nil => simp [digitsValue, fixedDigits]
  | cons c tail ih =>
    simp only [List.all_cons, Bool.and_eq_true] at valid
    obtain ⟨hc, ht⟩ := valid
    obtain ⟨suffixBound, suffixRender⟩ := ih ht
    have cBounds := Char.isDigit_iff_toNat.mp hc
    change 48 ≤ c.toNat ∧ c.toNat ≤ 57 at cBounds
    let head := c.toNat - 48
    have headBound : head < 10 := by dsimp only [head]; omega
    have headRender : head.digitChar = c := Char.toNat_inj.mp (by
      rw [Nat.toNat_digitChar_of_lt_ten headBound]
      dsimp only [head]
      omega)
    let place := 10 ^ tail.length
    have placePositive : 0 < place := Nat.pow_pos (by decide)
    change digitsValue tail < place at suffixBound
    have digitsEq : digitsValue (c :: tail) = place * head + digitsValue tail := digitsValue_cons c tail
    constructor
    · calc
        digitsValue (c :: tail) = place * head + digitsValue tail := digitsEq
        _ < place * (head + 1) := by rw [Nat.mul_succ]; exact Nat.add_lt_add_left suffixBound _
        _ ≤ place * 10 := Nat.mul_le_mul_left _ headBound
        _ = 10 ^ (c :: tail).length := by simp [place, Nat.pow_succ]
    · have quotient : digitsValue (c :: tail) / place = head := by
        rw [digitsEq, Nat.add_comm, Nat.add_mul_div_left _ _ placePositive,
          Nat.div_eq_of_lt suffixBound, Nat.zero_add]
      have remainder : digitsValue (c :: tail) % place = digitsValue tail := by
        rw [digitsEq, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt suffixBound]
      change (digitsValue (c :: tail) / place).digitChar ::
        fixedDigits tail.length (digitsValue (c :: tail) % place) = c :: tail
      rw [quotient, remainder, headRender, suffixRender]

theorem parseFixed_spec {width : Nat} {digits : List Char} {value : Nat}
    (h : parseFixed? width digits = some value) : value < 10 ^ width ∧ fixedDigits width value = digits := by
  unfold parseFixed? at h
  split at h
  next length =>
    unfold parseNat at h
    split at h
    next => contradiction
    next guard =>
      cases Option.some.inj h
      have all : digits.all Char.isDigit = true := by
        cases hv : digits.all Char.isDigit <;> simp_all
      simpa only [length] using digits_bound_and_render all
  next => contradiction

end Silmaril.Proofs.Formats.ISO8601.Date
