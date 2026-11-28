module

public import Silmaril.Languages.Starlark.Binary64.Defs

public section

namespace Silmaril.Proofs.Languages.Starlark.Binary64

open Silmaril.Languages.Starlark.Binary64

private theorem abs_magnitude (input : UInt64) : (abs input).toNat = input.toNat % 2 ^ 63 := by
  rw [abs, UInt64.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod input.toNat 63

theorem absolute_iff_abs (input output : UInt64) : Absolute input output ↔ abs input = output := by
  rw [Absolute, ← abs_magnitude input, UInt64.toNat_inj, eq_comm]

theorem truth_iff_truth (input : UInt64) (out : Bool) : Truth input out ↔ truth input = out := by
  have zero : abs input = 0 ↔ input.toNat % 2 ^ 63 = 0 := by
    rw [← UInt64.toNat_inj, abs_magnitude]
    rfl
  constructor
  · intro ran
    cases ran with
    | zero magnitude => simp [truth, zero.mpr magnitude]
    | nonzero magnitude => simp [truth, mt zero.mp magnitude]
  · intro result
    cases out with
    | false =>
      exact .zero (zero.mp (by simpa [truth] using result))
    | true =>
      exact .nonzero (mt zero.mpr (by simpa [truth] using result))

theorem truth_false_iff_signed_zero (input : UInt64) :
    truth input = false ↔ input = 0 ∨ input = 0x8000000000000000 := by
  rw [← truth_iff_truth]
  constructor
  · intro ran
    cases ran with
    | zero magnitude =>
      have bound : input.toNat < 0x10000000000000000 := input.toNat_lt_size
      change input.toNat % 0x8000000000000000 = 0 at magnitude
      have encoding : input.toNat = 0 ∨ input.toNat = 0x8000000000000000 := by omega
      exact encoding.imp UInt64.toNat_inj.mp UInt64.toNat_inj.mp
  · rintro (rfl | rfl) <;> exact .zero (by decide)

private theorem fields_valid (bits : UInt64) : (fields bits).Valid bits := by
  have bound : bits.toNat < 0x10000000000000000 := bits.toNat_lt_size
  unfold Fields.Valid fields
  dsimp only
  by_cases negative : 0x8000000000000000 ≤ bits.toNat <;> simp [negative] <;> omega

private theorem fields_unique {bits : UInt64} {left right : Fields}
    (l : left.Valid bits) (r : right.Valid bits) : left = right := by
  obtain ⟨leftSign, leftExp, leftFrac⟩ := left
  obtain ⟨rightSign, rightExp, rightFrac⟩ := right
  cases leftSign <;> cases rightSign <;> simp [Fields.Valid] at l r
  all_goals
    have exp : leftExp = rightExp := by omega
    have frac : leftFrac = rightFrac := by omega
    subst rightExp
    subst rightFrac
    first | rfl | omega

private theorem decode_eq_of_decodes {bits : UInt64} {value : Number}
    (ran : Decodes bits value) : decode bits = value := by
  cases ran with
  | zeroOrSubnormal valid zero => simp [decode, fields_unique (fields_valid bits) valid, zero]
  | normal valid positive finite =>
    simp [decode, fields_unique (fields_valid bits) valid, Nat.ne_of_lt finite,
      Nat.ne_of_gt positive]
  | infinite valid special zero => simp [decode, fields_unique (fields_valid bits) valid, special, zero]
  | nan valid special nonzero => simp [decode, fields_unique (fields_valid bits) valid, special, nonzero]

private theorem decodes_decode (bits : UInt64) : Decodes bits (decode bits) := by
  have valid := fields_valid bits
  unfold decode
  dsimp only
  by_cases special : (fields bits).exponent = 2047
  · by_cases zero : (fields bits).fraction = 0
    · simpa only [special, zero, ite_true] using Decodes.infinite valid special zero
    · simpa only [special, zero, ite_true, ite_false] using Decodes.nan valid special zero
  · by_cases zero : (fields bits).exponent = 0
    · rw [ite_eq_right special, ite_eq_left zero]
      exact .zeroOrSubnormal valid zero
    · have positive : 0 < (fields bits).exponent := Nat.pos_of_ne_zero zero
      have finite : (fields bits).exponent < 2047 := by have bound := valid.1; omega
      simpa only [special, zero, ite_false] using Decodes.normal valid positive finite

theorem decodes_iff_decode (bits : UInt64) (value : Number) :
    Decodes bits value ↔ decode bits = value :=
  ⟨decode_eq_of_decodes, fun h => h ▸ decodes_decode bits⟩

theorem orders_iff_compareNumbers (left right : Number) (order : Ordering) :
    Orders left right order ↔ compareNumbers left right = order := by
  cases left <;> cases right <;> cases order <;>
    simp [Orders, Number.Less, compareNumbers, Number.rank, Int.compare_eq_lt,
      Int.compare_eq_gt] <;> decide

end Silmaril.Proofs.Languages.Starlark.Binary64
