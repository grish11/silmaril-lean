module

public import Silmaril.Proofs.Machine.AArch64.Flags.AddWithCarry

/-!
# AArch64 flags after a subtraction: what N, Z, C and V say about the operands

Proofs for `Silmaril.Machine.AArch64.Flags.Thms`. SUBS and CMP compute
`addWithCarry x (~~~y) true`.

Method for `addWithCarry_not_true_lt`: at width `k + 1`, go through
`addWithCarry_eq_spec_of_pos` to the spec's N and V over `Int`, write `2 ^ (k + 1)` as
`2 * P`, turn every `toInt` into `toNat` or `toNat - 2 * P`, and let `omega` close each
case. Width zero is a single case.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.AArch64.Flags

open Silmaril.Machine.AArch64

/-- Z after SUBS: the operands are equal. -/
theorem addWithCarry_not_true_z {w : Nat} (x y : BitVec w) :
    (addWithCarry x (~~~y) true).2.z = decide (x = y) := by
  have h : (addWithCarry x (~~~y) true).2.z = ((addWithCarry x (~~~y) true).1 == 0#w) := rfl
  have hsub : x - y = 0#w ↔ x = y := by
    constructor
    · intro h0
      have := BitVec.sub_add_cancel x y
      rw [h0, BitVec.zero_add] at this
      exact this.symm
    · rintro rfl
      exact BitVec.sub_self _
  rw [h, addWithCarry_not_true_fst, Bool.eq_iff_iff]
  simpa using hsub

/-- N != V after SUBS: `x < y` as signed numbers. -/
theorem addWithCarry_not_true_lt {w : Nat} (x y : BitVec w) :
    ((addWithCarry x (~~~y) true).2.n != (addWithCarry x (~~~y) true).2.v) =
      decide (x.toInt < y.toInt) := by
  cases w with
  | zero => rw [BitVec.eq_nil x, BitVec.eq_nil y]; rfl
  | succ k =>
    rw [addWithCarry_eq_spec_of_pos (Nat.succ_pos k)]
    simp only [Spec.addWithCarry]
    generalize hr : BitVec.ofNat (k + 1) (x.toNat + (~~~y).toNat + true.toNat) = r
    have hrn : r.toNat = (x.toNat + (~~~y).toNat + 1) % 2 ^ (k + 1) := by subst hr; simp
    have hxi := BitVec.toInt_eq_toNat_cond x
    have hyi := BitVec.toInt_eq_toNat_cond y
    have hni := BitVec.toInt_eq_toNat_cond (~~~y)
    have hri := BitVec.toInt_eq_toNat_cond r
    have hP : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
    have hx := x.isLt
    have hy := y.isLt
    rw [BitVec.toNat_not] at hrn hni
    rw [hP] at hrn hx hy hxi hyi hni hri
    generalize 2 ^ k = P at *
    have hm : r.toNat + y.toNat = x.toNat ∨ r.toNat + y.toNat = x.toNat + 2 * P := by
      by_cases h : y.toNat ≤ x.toNat
      · left
        rw [hrn, show x.toNat + (2 * P - 1 - y.toNat) + 1 = (x.toNat - y.toNat) + 2 * P by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        omega
      · right; rw [hrn, Nat.mod_eq_of_lt (by omega)]; omega
    clear hrn hr
    rw [Bool.eq_iff_iff]
    split at hxi <;> split at hyi <;> split at hni <;> split at hri <;>
      simp [hxi, hyi, hni, hri] <;> omega

/-- Z or N != V after SUBS: `x ≤ y` as signed numbers. -/
theorem addWithCarry_not_true_le {w : Nat} (x y : BitVec w) :
    ((addWithCarry x (~~~y) true).2.z ||
        (addWithCarry x (~~~y) true).2.n != (addWithCarry x (~~~y) true).2.v) =
      decide (x.toInt ≤ y.toInt) := by
  rw [addWithCarry_not_true_z, addWithCarry_not_true_lt, Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, decide_eq_true_eq, ← BitVec.toInt_inj]
  omega

/-! ## Conditions after SUBS

Each condition is first unfolded to its flag formula (by `rfl`, or by `decide` over the 16
flag values), then rewritten with `addWithCarry_not_true_z`, `_lt`, `_le` and `_c`. EQ, LT
and CS are those lemmas themselves. -/

private theorem cond_ge (f : NZCV) : condHolds 0b1010#4 f = !(f.n != f.v) := by
  rcases f with ⟨n, z, c, v⟩; revert n z c v; decide

private theorem cond_le (f : NZCV) : condHolds 0b1101#4 f = (f.z || f.n != f.v) := by
  rcases f with ⟨n, z, c, v⟩; revert n z c v; decide

private theorem cond_gt (f : NZCV) : condHolds 0b1100#4 f = !(f.z || f.n != f.v) := by
  rcases f with ⟨n, z, c, v⟩; revert n z c v; decide

/-- LT after SUBS: `x < y`, signed. -/
theorem condHolds_lt_subs {w : Nat} (x y : BitVec w) :
    condHolds 0b1011#4 (addWithCarry x (~~~y) true).2 = decide (x.toInt < y.toInt) :=
  addWithCarry_not_true_lt x y

/-- GE after SUBS: `x ≥ y`, signed. -/
theorem condHolds_ge_subs {w : Nat} (x y : BitVec w) :
    condHolds 0b1010#4 (addWithCarry x (~~~y) true).2 = decide (y.toInt ≤ x.toInt) := by
  rw [cond_ge, addWithCarry_not_true_lt, Bool.eq_iff_iff]
  simp

/-- LE after SUBS: `x ≤ y`, signed. -/
theorem condHolds_le_subs {w : Nat} (x y : BitVec w) :
    condHolds 0b1101#4 (addWithCarry x (~~~y) true).2 = decide (x.toInt ≤ y.toInt) := by
  rw [cond_le, addWithCarry_not_true_le]

/-- GT after SUBS: `x > y`, signed. -/
theorem condHolds_gt_subs {w : Nat} (x y : BitVec w) :
    condHolds 0b1100#4 (addWithCarry x (~~~y) true).2 = decide (y.toInt < x.toInt) := by
  rw [cond_gt, addWithCarry_not_true_le, Bool.eq_iff_iff]
  simp

/-- EQ after SUBS: `x = y`. -/
theorem condHolds_eq_subs {w : Nat} (x y : BitVec w) :
    condHolds 0b0000#4 (addWithCarry x (~~~y) true).2 = decide (x = y) :=
  addWithCarry_not_true_z x y

/-- NE after SUBS: `x ≠ y`. -/
theorem condHolds_ne_subs {w : Nat} (x y : BitVec w) :
    condHolds 0b0001#4 (addWithCarry x (~~~y) true).2 = decide (x ≠ y) := by
  have h : condHolds 0b0001#4 (addWithCarry x (~~~y) true).2 =
      !(addWithCarry x (~~~y) true).2.z := rfl
  rw [h, addWithCarry_not_true_z]
  simp

/-- CS (HS) after SUBS: `x ≥ y`, unsigned. False at width zero. -/
theorem condHolds_cs_subs {w : Nat} (hw : 0 < w) (x y : BitVec w) :
    condHolds 0b0010#4 (addWithCarry x (~~~y) true).2 = decide (y.toNat ≤ x.toNat) :=
  addWithCarry_not_true_c hw x y

/-- CC (LO) after SUBS: `x < y`, unsigned. False at width zero. -/
theorem condHolds_cc_subs {w : Nat} (hw : 0 < w) (x y : BitVec w) :
    condHolds 0b0011#4 (addWithCarry x (~~~y) true).2 = decide (x.toNat < y.toNat) := by
  have h : condHolds 0b0011#4 (addWithCarry x (~~~y) true).2 =
      !(addWithCarry x (~~~y) true).2.c := rfl
  rw [h, addWithCarry_not_true_c hw, Bool.eq_iff_iff]
  simp

/-- HI after SUBS: `x > y`, unsigned. -/
theorem condHolds_hi_subs {w : Nat} (x y : BitVec w) :
    condHolds 0b1000#4 (addWithCarry x (~~~y) true).2 = decide (y.toNat < x.toNat) := by
  cases w with
  | zero => rw [BitVec.eq_nil x, BitVec.eq_nil y]; rfl
  | succ k =>
    have h : condHolds 0b1000#4 (addWithCarry x (~~~y) true).2 =
        ((addWithCarry x (~~~y) true).2.c && !(addWithCarry x (~~~y) true).2.z) := rfl
    rw [h, addWithCarry_not_true_c (Nat.succ_pos k), addWithCarry_not_true_z, Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not,
      ← BitVec.toNat_inj]
    omega

/-- LS after SUBS: `x ≤ y`, unsigned. -/
theorem condHolds_ls_subs {w : Nat} (x y : BitVec w) :
    condHolds 0b1001#4 (addWithCarry x (~~~y) true).2 = decide (x.toNat ≤ y.toNat) := by
  have hhi := condHolds_hi_subs x y
  have h : condHolds 0b1001#4 (addWithCarry x (~~~y) true).2 =
      !condHolds 0b1000#4 (addWithCarry x (~~~y) true).2 := by
    generalize (addWithCarry x (~~~y) true).2 = f
    rcases f with ⟨n, z, c, v⟩; revert n z c v; decide
  rw [h, hhi, Bool.eq_iff_iff]
  simp

end Silmaril.Proofs.Machine.AArch64.Flags
