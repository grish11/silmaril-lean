module

public import Silmaril.Machine.AArch64.Flags.Defs

/-!
# AArch64 `addWithCarry` agrees with Arm's arithmetic definition

Proofs for `Silmaril.Machine.AArch64.Flags.Thms`.

Method for `addWithCarry_eq_spec_of_pos`: write the width as `k + 1` and `2 ^ (k + 1)` as
`2 * P`. Every top bit becomes `P ≤ toNat`, every `toInt` becomes `toNat` or
`toNat - 2 * P`, and the wrapped result is the sum or the sum minus `2 * P`. The remaining
goals are linear, and `omega` closes each case.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.AArch64.Flags

open Silmaril.Machine.AArch64

/-- With a positive width, the bit-level sum is Arm's `unsigned_sum[N-1:0]`. -/
theorem result_eq {w : Nat} (hw : 0 < w) (x y : BitVec w) (c : Bool) :
    x + y + (BitVec.ofBool c).setWidth w = BitVec.ofNat w (x.toNat + y.toNat + c.toNat) := by
  apply BitVec.eq_of_toNat_eq
  have h2 : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
  have hc : c.toNat < 2 ^ w := by cases c <;> simp <;> omega
  simp [BitVec.toNat_add, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hc]

/-- The bit-level flags equal Arm's arithmetic flags at every positive width. -/
theorem addWithCarry_eq_spec_of_pos {w : Nat} (hw : 0 < w) (x y : BitVec w) (c : Bool) :
    addWithCarry x y c = Spec.addWithCarry x y c := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
  simp only [addWithCarry, Spec.addWithCarry, result_eq hw]
  generalize hr : BitVec.ofNat (k + 1) (x.toNat + y.toNat + c.toNat) = r
  have hrn : r.toNat = (x.toNat + y.toNat + c.toNat) % 2 ^ (k + 1) := by subst hr; simp
  have hz : (r == 0#(k + 1)) = decide (r.toNat = 0) := by
    rw [Bool.eq_iff_iff]; simp [BitVec.toNat_eq]
  simp only [hz, BitVec.msb_and, BitVec.msb_or, BitVec.msb_xor, BitVec.msb_not]
  simp only [BitVec.msb_eq_decide, Nat.add_sub_cancel, Prod.mk.injEq, NZCV.mk.injEq, true_and]
  have hxi := BitVec.toInt_eq_toNat_cond x
  have hyi := BitVec.toInt_eq_toNat_cond y
  have hri := BitVec.toInt_eq_toNat_cond r
  have hP : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
  have hx := x.isLt
  have hy := y.isLt
  have hc : c.toNat ≤ 1 := by cases c <;> simp
  rw [hP] at hrn hx hy hxi hyi hri
  generalize 2 ^ k = P at *
  have hm : r.toNat = x.toNat + y.toNat + c.toNat ∨
      r.toNat + 2 * P = x.toNat + y.toNat + c.toNat := by
    by_cases h : x.toNat + y.toNat + c.toNat < 2 * P
    · left; rw [hrn, Nat.mod_eq_of_lt h]
    · right; rw [hrn, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  clear hrn hr
  rw [show decide (0 < k + 1) = true from by simp, Bool.true_and]
  split at hxi <;> split at hyi <;> split at hri <;>
    by_cases h1 : P ≤ x.toNat <;> by_cases h2 : P ≤ y.toNat <;> by_cases h3 : P ≤ r.toNat <;>
    simp [h1, h2, h3, hxi, hyi, hri] <;> omega

/-- Arm's `c` is set exactly when the unsigned sum does not fit in `w` bits. -/
theorem spec_c {w : Nat} (x y : BitVec w) (c : Bool) :
    (Spec.addWithCarry x y c).2.c = decide (2 ^ w ≤ x.toNat + y.toNat + c.toNat) := by
  simp only [Spec.addWithCarry, BitVec.toNat_ofNat]
  by_cases h : x.toNat + y.toNat + c.toNat < 2 ^ w
  · simp [Nat.mod_eq_of_lt h, Nat.not_le.mpr h]
  · have := Nat.mod_lt (x.toNat + y.toNat + c.toNat) (Nat.two_pow_pos w)
    simp [Nat.le_of_not_lt h]
    omega

/-- **C = no borrow.** For SUBS (`x + NOT y + 1`) the carry is set exactly when `y ≤ x`
as unsigned numbers. -/
theorem addWithCarry_not_true_c {w : Nat} (hw : 0 < w) (x y : BitVec w) :
    (addWithCarry x (~~~y) true).2.c = decide (y.toNat ≤ x.toNat) := by
  rw [addWithCarry_eq_spec_of_pos hw, spec_c, BitVec.toNat_not]
  have := y.isLt
  simp only [Bool.toNat_true, decide_eq_decide]
  omega

/-- C after ADDS is the unsigned overflow of `x + y`, at every width. -/
theorem addWithCarry_false_c {w : Nat} (x y : BitVec w) :
    (addWithCarry x y false).2.c = decide (2 ^ w ≤ x.toNat + y.toNat) := by
  cases w with
  | zero => rw [BitVec.eq_nil x, BitVec.eq_nil y]; rfl
  | succ k => rw [addWithCarry_eq_spec_of_pos (Nat.succ_pos k), spec_c]; rfl

/-- `x + NOT y + 1` is `x - y`. -/
theorem addWithCarry_not_true_fst {w : Nat} (x y : BitVec w) :
    (addWithCarry x (~~~y) true).1 = x - y := by
  simp only [addWithCarry]
  rw [BitVec.sub_eq_add_neg, BitVec.neg_eq_not_add, BitVec.add_assoc]
  congr 2
  apply BitVec.eq_of_toNat_eq
  simp

end Silmaril.Proofs.Machine.AArch64.Flags
