module

public import Silmaril.Formats.JsonNumbers.Defs
public import Silmaril.Formats.JsonBytes.Thms

/-! # Proofs: number-token languages (`Silmaril.Formats.JsonNumbers.Thms`) -/

@[expose] public section

namespace Silmaril.Proofs.Formats.JsonNumbers.Tokens

open RegularExpression Silmaril.Formats.Utf8 Silmaril.Formats.JsonBytes
open Silmaril.Formats.JsonNumbers

/-! ## Lexical integers -/

theorem mem_digit {w : List UInt8} : w ∈ digit.matches' ↔ ∃ b, w = [b] ∧ isDigit b = true := by
  rw [digit, mem_byteRange]
  simp [isDigit]

theorem mem_star_digit {w : List UInt8} : w ∈ (star digit).matches' → ∀ b ∈ w, isDigit b = true := by
  rw [matches', Language.mem_kstar]
  rintro ⟨L, rfl, hL⟩ b hb
  obtain ⟨y, hy, hby⟩ := List.mem_flatten.mp hb
  obtain ⟨d, rfl, hd⟩ := mem_digit.mp (hL y hy)
  rw [List.mem_singleton] at hby
  exact hby ▸ hd

/-- An `int` is a non-empty string of digits. -/
theorem int_digits {w : List UInt8} (h : w ∈ int.matches') :
    ∃ d t, w = d :: t ∧ isDigit d = true ∧ ∀ b ∈ t, isDigit b = true := by
  simp only [int, matches'_add, matches'_mul, matches'_char, Language.mem_add,
    Language.mem_mul] at h
  rcases h with h | ⟨a, ha, t, ht, rfl⟩
  · obtain rfl : w = [0x30] := h
    exact ⟨0x30, [], rfl, by decide, by simp⟩
  · obtain ⟨d, rfl, hd⟩ := mem_byteRange.mp ha
    refine ⟨d, t, rfl, ?_, mem_star_digit ht⟩
    simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨UInt8.le_trans (by decide) hd.1, hd.2⟩

theorem mem_integerToken {w : List UInt8} :
    w ∈ integerToken ↔ w ∈ int.matches' ∨ ∃ t ∈ int.matches', w = 0x2D :: t := by
  simp only [integerToken, matches'_mul, matches'_add, matches'_char, Language.mem_mul,
    Language.mem_add]
  constructor
  · rintro ⟨a, ha, t, ht, rfl⟩
    rcases ha with ha | ha
    · obtain rfl : a = [] := ha
      exact Or.inl ht
    · obtain rfl : a = [0x2D] := ha
      exact Or.inr ⟨t, ht, rfl⟩
  · rintro (h | ⟨t, ht, rfl⟩)
    · exact ⟨[], Or.inl rfl, w, h, rfl⟩
    · exact ⟨[0x2D], Or.inr rfl, t, ht, rfl⟩

theorem integerToken_le_rfc : integerToken ≤ rfc := by
  intro w h
  simp only [integerToken, rfc, number, matches'_mul, matches'_add] at h ⊢
  refine ⟨w ++ [], ⟨w, h, [], Or.inl rfl, rfl⟩, [], Or.inl rfl, by simp⟩

/-! ## Values of lexical integers -/

theorem takeWhile_of_all {l : List UInt8} {q : UInt8 → Bool} (h : ∀ x ∈ l, q x = true) :
    l.takeWhile q = l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.takeWhile_cons, ite_eq_left_of_eq_true _ _ (eq_true (h a (by simp))), ih (fun x hx => h x (by simp [hx]))]

theorem dropWhile_of_all {l : List UInt8} {q : UInt8 → Bool} (h : ∀ x ∈ l, q x = true) :
    l.dropWhile q = [] := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.dropWhile_cons, ite_eq_left_of_eq_true _ _ (eq_true (h a (by simp))), ih (fun x hx => h x (by simp [hx]))]

theorem unsignedParts_digits {d : UInt8} {t : List UInt8} (hd : isDigit d = true)
    (ht : ∀ b ∈ t, isDigit b = true) : unsignedParts (d :: t) = (d :: t, [], 0) := by
  have h1 : (d :: t).takeWhile isDigit = d :: t := takeWhile_of_all (by
    intro b hb; rcases List.mem_cons.mp hb with rfl | hb; exacts [hd, ht b hb])
  have h2 : (d :: t).dropWhile isDigit = [] := dropWhile_of_all (by
    intro b hb; rcases List.mem_cons.mp hb with rfl | hb; exacts [hd, ht b hb])
  simp [unsignedParts, h1, h2]

theorem unsignedValue_digits {d : UInt8} {t : List UInt8} (hd : isDigit d = true)
    (ht : ∀ b ∈ t, isDigit b = true) : unsignedValue (d :: t) = digitsValue (d :: t) := by
  simp [unsignedValue, unsignedParts_digits hd ht]

theorem value_eq_intValue {w : List UInt8} (h : w ∈ integerToken) :
    value w = (intValue w : ℚ) := by
  rcases mem_integerToken.mp h with h | ⟨t, ht, rfl⟩
  · obtain ⟨d, t, rfl, hd, ht⟩ := int_digits h
    have hd' : d ≠ 0x2D := by rintro rfl; exact absurd hd (by decide)
    rw [value.eq_def, intValue.eq_def]
    split
    · rename_i r hr; simp only [List.cons.injEq] at hr; exact absurd hr.1 hd'
    · simp [unsignedValue_digits hd ht]
  · obtain ⟨d, t, rfl, hd, ht⟩ := int_digits ht
    simp [value, intValue, unsignedValue_digits hd ht]

theorem integerToken_le_integralNumber : integerToken ≤ integralNumber := by
  intro w h
  refine ⟨integerToken_le_rfc h, ?_⟩
  rw [value_eq_intValue h]
  exact Rat.den_intCast _

theorem integralNumber_le_rfc : integralNumber ≤ rfc := fun _ h => h.1

/-! ## Bounded and binary64 integers -/

theorem boundedInteger_le_integerToken (lo hi : Int) : boundedInteger lo hi ≤ integerToken :=
  fun _ h => h.1

theorem boundedInteger_mono {lo hi lo' hi' : Int} (hl : lo' ≤ lo) (hh : hi ≤ hi') :
    boundedInteger lo hi ≤ boundedInteger lo' hi' :=
  fun _ ⟨h, h₁, h₂⟩ => ⟨h, le_trans hl h₁, le_trans h₂ hh⟩

theorem isBinary64Integer_iff {n : Int} :
    IsBinary64Integer n ↔ ∃ e < 972, 2 ^ e ∣ n.natAbs ∧ n.natAbs / 2 ^ e < 2 ^ 53 := by
  constructor
  · rintro ⟨e, he, m, hm, h⟩
    refine ⟨e, by omega, ⟨m, by rw [h, Nat.mul_comm]⟩, ?_⟩
    rw [h, Nat.mul_div_cancel _ (Nat.two_pow_pos e)]
    exact hm
  · rintro ⟨e, he, hd, hm⟩
    exact ⟨e, by omega, _, hm, (Nat.div_mul_cancel hd).symm⟩

theorem isBinary64Integer_of_safe {n : Int} (h₁ : -(2 ^ 53 - 1) ≤ n) (h₂ : n ≤ 2 ^ 53 - 1) :
    IsBinary64Integer n :=
  ⟨0, by omega, n.natAbs, by omega, by simp⟩

theorem safeInteger_le_binary64Integer : safeInteger ≤ binary64Integer :=
  fun _ ⟨h, h₁, h₂⟩ => ⟨h, isBinary64Integer_of_safe h₁ h₂⟩

/-! ## Non-finite extensions -/

theorem rfc_le_withPythonInfinity : rfc ≤ withPythonInfinity := by
  intro w h
  simp only [withPythonInfinity, matches'_add]
  exact Or.inl h

theorem withPythonInfinity_le_withPythonNonFinite : withPythonInfinity ≤ withPythonNonFinite := by
  intro w h
  simp only [withPythonInfinity, withPythonNonFinite, matches'_add] at h ⊢
  exact Or.inl h

end Silmaril.Proofs.Formats.JsonNumbers.Tokens

end
