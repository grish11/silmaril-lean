module

public import Silmaril.Machine.AArch64.Flags.Defs
import Silmaril.Proofs.Machine.AArch64.Flags.Compare

/-!
# AArch64 condition flags: agreement with Arm's definitions, and what the flags mean

* `addWithCarry_eq_spec`, `addWithCarry_eq_spec_64`: at 32 and 64 bits, the bit-level
  `addWithCarry` equals `Spec.addWithCarry`, Arm's `AddWithCarry` over `Nat` and `Int`.
  `addWithCarry_eq_spec_of_pos` is the same for every width greater than zero. At width
  zero they differ: with carry-in set, the spec's C and V are both 1 and the bit formulas
  give 0 for both.
  Proofs: `Silmaril.Proofs.Machine.AArch64.Flags`.
* `addWithCarry_not_true_c`: **C = no borrow.** SUBS and CMP compute
  `AddWithCarry(x, NOT y, '1')` (Arm A64 ISA XML 2026-09, SUBS (shifted register)), so C is
  set exactly when `y ≤ x` as unsigned numbers. x86 sets CF to the opposite (borrow).
  The Arm documentation states no A64 prose rule for this; it follows from the pseudocode.
* `addWithCarry_not_true_z`, `addWithCarry_not_true_lt`, `addWithCarry_not_true_le`: what
  Z, N and V mean after SUBS and CMP: Z is `x = y`, `N != V` is `x < y` as signed numbers,
  and `Z || N != V` is `x ≤ y` as signed numbers.
* `condHolds_eq_subs`, `_ne_subs`, `_lt_subs`, `_ge_subs`, `_le_subs`, `_gt_subs`,
  `_hi_subs`, `_ls_subs`, `_cs_subs`, `_cc_subs`: after SUBS or CMP of `x` and `y`, each of
  these ten condition codes holds exactly when a comparison of `x` and `y` is true. For
  eight of them it is the comparison named in the code's row of Table C1-1; for CS and CC
  the row says only "Carry set" and "Carry clear", and the comparison is the no-borrow
  reading of C (`addWithCarry_not_true_c`). These are statements about the bit-level
  `addWithCarry`: for it, only CS and CC need a positive width.
* `condHolds_eq_spec`: `condHolds` (Arm's `ConditionHolds` pseudocode) equals
  `Spec.condHolds` (Arm ARM C1.2.4, Table C1-1) for all 16 conditions and all flag values.
-/

@[expose] public section

namespace Silmaril.Machine.AArch64

/-! ## `addWithCarry` -/

/-- The bit-level `addWithCarry` equals Arm's arithmetic `AddWithCarry` at every
positive width. -/
theorem addWithCarry_eq_spec_of_pos {w : Nat} (hw : 0 < w) (x y : BitVec w) (c : Bool) :
    addWithCarry x y c = Spec.addWithCarry x y c :=
  Silmaril.Proofs.Machine.AArch64.Flags.addWithCarry_eq_spec_of_pos hw x y c

/-- **32-bit agreement** (the `W` forms of ADDS, SUBS, CMP). -/
theorem addWithCarry_eq_spec (x y : BitVec 32) (c : Bool) :
    addWithCarry x y c = Spec.addWithCarry x y c :=
  addWithCarry_eq_spec_of_pos (by decide) x y c

/-- **64-bit agreement** (the `X` forms of ADDS, SUBS, CMP). -/
theorem addWithCarry_eq_spec_64 (x y : BitVec 64) (c : Bool) :
    addWithCarry x y c = Spec.addWithCarry x y c :=
  addWithCarry_eq_spec_of_pos (by decide) x y c

/-- Arm's C is set exactly when the unsigned sum does not fit in `w` bits. -/
theorem Spec.addWithCarry_c {w : Nat} (x y : BitVec w) (c : Bool) :
    (Spec.addWithCarry x y c).2.c = decide (2 ^ w ≤ x.toNat + y.toNat + c.toNat) :=
  Silmaril.Proofs.Machine.AArch64.Flags.spec_c x y c

/-- The result of ADDS is the wrapped sum. -/
theorem addWithCarry_false_fst {w : Nat} (x y : BitVec w) :
    (addWithCarry x y false).1 = x + y := by
  simp [addWithCarry]

/-- The result of SUBS is the wrapped difference. -/
theorem addWithCarry_not_true_fst {w : Nat} (x y : BitVec w) :
    (addWithCarry x (~~~y) true).1 = x - y :=
  Silmaril.Proofs.Machine.AArch64.Flags.addWithCarry_not_true_fst x y

/-- **C = no borrow.** For SUBS and CMP the carry is set exactly when `y ≤ x` as
unsigned numbers. -/
theorem addWithCarry_not_true_c {w : Nat} (hw : 0 < w) (x y : BitVec w) :
    (addWithCarry x (~~~y) true).2.c = decide (y.toNat ≤ x.toNat) :=
  Silmaril.Proofs.Machine.AArch64.Flags.addWithCarry_not_true_c hw x y

/-- For ADDS the carry is the unsigned overflow of `x + y`, at every width. -/
theorem addWithCarry_false_c {w : Nat} (x y : BitVec w) :
    (addWithCarry x y false).2.c = decide (2 ^ w ≤ x.toNat + y.toNat) :=
  Silmaril.Proofs.Machine.AArch64.Flags.addWithCarry_false_c x y

/-! ## What the flags mean after SUBS and CMP

SUBS and CMP compute `addWithCarry x (~~~y) true`. `toInt` reads a bit vector as a signed
(two's complement) number, `toNat` as an unsigned one. -/

/-- **Z = equal.** After SUBS and CMP, Z is set exactly when `x = y`. -/
theorem addWithCarry_not_true_z {w : Nat} (x y : BitVec w) :
    (addWithCarry x (~~~y) true).2.z = decide (x = y) :=
  Silmaril.Proofs.Machine.AArch64.Flags.addWithCarry_not_true_z x y

/-- **N != V = signed less than.** After SUBS and CMP, N and V differ exactly when
`x < y` as signed numbers. N alone is not enough: when the subtraction overflows, the
sign of the result is wrong and V says so. -/
theorem addWithCarry_not_true_lt {w : Nat} (x y : BitVec w) :
    ((addWithCarry x (~~~y) true).2.n != (addWithCarry x (~~~y) true).2.v) =
      decide (x.toInt < y.toInt) :=
  Silmaril.Proofs.Machine.AArch64.Flags.addWithCarry_not_true_lt x y

/-- **Z || N != V = signed less than or equal.** -/
theorem addWithCarry_not_true_le {w : Nat} (x y : BitVec w) :
    ((addWithCarry x (~~~y) true).2.z ||
        (addWithCarry x (~~~y) true).2.n != (addWithCarry x (~~~y) true).2.v) =
      decide (x.toInt ≤ y.toInt) :=
  Silmaril.Proofs.Machine.AArch64.Flags.addWithCarry_not_true_le x y

/-! ## `condHolds` -/

/-- Arm's `ConditionHolds` pseudocode agrees with Table C1-1, for every condition and
every flag value (256 cases, checked by the kernel). -/
theorem condHolds_eq_spec (cond : BitVec 4) (f : NZCV) :
    condHolds cond f = Spec.condHolds cond f := by
  rcases f with ⟨n, z, c, v⟩
  revert cond n z c v; decide

/-- CC/LO (`0011`): carry clear. Used by CSINV in `sat_add_u32`. -/
theorem condHolds_cc (f : NZCV) : condHolds 0b0011#4 f = !f.c := rfl

/-- LT (`1011`): `N != V`. Used by B.LT in `clamp_i32`. -/
theorem condHolds_lt (f : NZCV) : condHolds 0b1011#4 f = (f.n != f.v) := rfl

/-- LE (`1101`): `!(Z == 0 && N == V)`. Used by CSEL in `clamp_i32`. -/
theorem condHolds_le (f : NZCV) : condHolds 0b1101#4 f = (f.z || f.n != f.v) := by
  rcases f with ⟨n, z, c, v⟩
  cases n <;> cases z <;> cases v <;> rfl

/-- AL (`1110`) always holds. -/
theorem condHolds_al (f : NZCV) : condHolds 0b1110#4 f = true := rfl

/-- NV (`1111`) always holds too: it behaves as AL (Table C1-1, footnote b). -/
theorem condHolds_nv (f : NZCV) : condHolds 0b1111#4 f = true := rfl

/-! ## Conditions after SUBS and CMP

One theorem for each of the ten condition codes that read as a comparison (MI, PL, VS, VC,
AL and NV have none). After SUBS or CMP, `x` is the first operand and `y` the second
(`operand1` and `operand2` before `NOT` in Arm's SUBS pseudocode). The quoted words are the
"Meaning (integer)" column of Arm ARM C1.2.4, Table C1-1. For CS and CC that column says
only "Carry set" and "Carry clear"; the unsigned comparison is the no-borrow reading of C
(`addWithCarry_not_true_c`). -/

/-- EQ (`0000`, "Equal"): `x = y`. -/
theorem condHolds_eq_subs {w : Nat} (x y : BitVec w) :
    condHolds 0b0000#4 (addWithCarry x (~~~y) true).2 = decide (x = y) :=
  Silmaril.Proofs.Machine.AArch64.Flags.condHolds_eq_subs x y

/-- NE (`0001`, "Not equal"): `x ≠ y`. -/
theorem condHolds_ne_subs {w : Nat} (x y : BitVec w) :
    condHolds 0b0001#4 (addWithCarry x (~~~y) true).2 = decide (x ≠ y) :=
  Silmaril.Proofs.Machine.AArch64.Flags.condHolds_ne_subs x y

/-- CS or HS (`0010`, "Carry set"): `y ≤ x, unsigned (no borrow)`. Needs a positive width:
at width zero the bit-level C is 0 where the spec's is 1. -/
theorem condHolds_cs_subs {w : Nat} (hw : 0 < w) (x y : BitVec w) :
    condHolds 0b0010#4 (addWithCarry x (~~~y) true).2 = decide (y.toNat ≤ x.toNat) :=
  Silmaril.Proofs.Machine.AArch64.Flags.condHolds_cs_subs hw x y

/-- CC or LO (`0011`, "Carry clear"): `x < y, unsigned (borrow)`. Needs a positive width:
at width zero the bit-level C is 0 where the spec's is 1. -/
theorem condHolds_cc_subs {w : Nat} (hw : 0 < w) (x y : BitVec w) :
    condHolds 0b0011#4 (addWithCarry x (~~~y) true).2 = decide (x.toNat < y.toNat) :=
  Silmaril.Proofs.Machine.AArch64.Flags.condHolds_cc_subs hw x y

/-- HI (`1000`, "Unsigned higher"): `x > y, unsigned`. -/
theorem condHolds_hi_subs {w : Nat} (x y : BitVec w) :
    condHolds 0b1000#4 (addWithCarry x (~~~y) true).2 = decide (y.toNat < x.toNat) :=
  Silmaril.Proofs.Machine.AArch64.Flags.condHolds_hi_subs x y

/-- LS (`1001`, "Unsigned lower or same"): `x ≤ y, unsigned`. -/
theorem condHolds_ls_subs {w : Nat} (x y : BitVec w) :
    condHolds 0b1001#4 (addWithCarry x (~~~y) true).2 = decide (x.toNat ≤ y.toNat) :=
  Silmaril.Proofs.Machine.AArch64.Flags.condHolds_ls_subs x y

/-- GE (`1010`, "Signed greater than or equal"): `x ≥ y, signed`. -/
theorem condHolds_ge_subs {w : Nat} (x y : BitVec w) :
    condHolds 0b1010#4 (addWithCarry x (~~~y) true).2 = decide (y.toInt ≤ x.toInt) :=
  Silmaril.Proofs.Machine.AArch64.Flags.condHolds_ge_subs x y

/-- LT (`1011`, "Signed less than"): `x < y, signed`. -/
theorem condHolds_lt_subs {w : Nat} (x y : BitVec w) :
    condHolds 0b1011#4 (addWithCarry x (~~~y) true).2 = decide (x.toInt < y.toInt) :=
  Silmaril.Proofs.Machine.AArch64.Flags.condHolds_lt_subs x y

/-- GT (`1100`, "Signed greater than"): `x > y, signed`. -/
theorem condHolds_gt_subs {w : Nat} (x y : BitVec w) :
    condHolds 0b1100#4 (addWithCarry x (~~~y) true).2 = decide (y.toInt < x.toInt) :=
  Silmaril.Proofs.Machine.AArch64.Flags.condHolds_gt_subs x y

/-- LE (`1101`, "Signed less than or equal"): `x ≤ y, signed`. -/
theorem condHolds_le_subs {w : Nat} (x y : BitVec w) :
    condHolds 0b1101#4 (addWithCarry x (~~~y) true).2 = decide (x.toInt ≤ y.toInt) :=
  Silmaril.Proofs.Machine.AArch64.Flags.condHolds_le_subs x y

end Silmaril.Machine.AArch64
