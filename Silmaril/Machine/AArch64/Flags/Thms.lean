module

public import Silmaril.Machine.AArch64.Flags.Defs
import Silmaril.Proofs.Machine.AArch64.Flags.AddWithCarry

/-!
# AArch64 condition flags: agreement with Arm's definitions

* `addWithCarry_eq_spec`, `addWithCarry_eq_spec_64`: at 32 and 64 bits, the bit-level
  `addWithCarry` equals `Spec.addWithCarry`, Arm's `AddWithCarry` over `Nat` and `Int`.
  `addWithCarry_eq_spec_of_pos` is the same for every width greater than zero. At width
  zero they differ: with carry-in set, Arm's C is 1 and the bit formula gives 0.
  Proofs: `Silmaril.Proofs.Machine.AArch64.Flags`.
* `addWithCarry_not_true_c`: **C = no borrow.** SUBS and CMP compute
  `AddWithCarry(x, NOT y, '1')` (Arm A64 ISA XML 2026-09, SUBS (shifted register)), so C is
  set exactly when `y ≤ x` as unsigned numbers. x86 sets CF to the opposite (borrow).
  The Arm documentation states no A64 prose rule for this; it follows from the pseudocode.
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

/-- For ADDS the carry is the unsigned overflow of `x + y`. -/
theorem addWithCarry_false_c {w : Nat} (hw : 0 < w) (x y : BitVec w) :
    (addWithCarry x y false).2.c = decide (2 ^ w ≤ x.toNat + y.toNat) := by
  rw [addWithCarry_eq_spec_of_pos hw, Spec.addWithCarry_c]
  rfl

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

end Silmaril.Machine.AArch64
