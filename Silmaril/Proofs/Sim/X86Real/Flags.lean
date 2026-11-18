module

public import Silmaril.Sim.X86Real.Defs
public import Silmaril.X86.Flags

/-!
# The simulator's ALU flags are Silmaril's x86 flags

`aluFlags_add`, `aluFlags_sub`: the six flag bits the core of `simG`/`simM` computes for 64-bit
`add` (op `0`) and `sub`/`cmp` (ops `5`, `7`) are exactly `Silmaril.X86.addFlags` /
`subFlags` (the flags of `Silmaril.X86.Ext`'s `ADD`/`SUB`/`CMP`, `Ext.addFlagsN_eq`), all six
defined. A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Sim.X86Real

set_option linter.unusedSimpArgs false

open Silmaril.X86 (parity addCarry addAdjust isZero sign addOverflow subBorrow subAdjust
  subOverflow)

/-- A defined flag as the simulator's `0`/`1`. -/
def fl (b : Bool) : BitVec 32 := if b then 1#32 else 0#32

/-- The six status flags of a Silmaril flag record (all defined for `addFlags`/`subFlags`). -/
def bitsOf (F : Silmaril.X86.Flags) :
    BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 :=
  (fl (F.carry.getD false), fl (F.parity.getD false), fl (F.adjust.getD false),
   fl (F.zero.getD false), fl (F.sign.getD false), fl (F.overflow.getD false))

theorem and_sb64 (x : BitVec 64) : (x &&& sb64 = 0#64) ↔ x.msb = false := by
  rw [BitVec.msb_eq_getLsbD_last]
  constructor
  · intro h
    have := congrArg (fun v => v.getLsbD 63) h
    simpa [sb64, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft] using this
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [sb64, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero]
    by_cases h63 : i = 63
    · subst h63; simpa using h
    · simp [h63]; omega

theorem sbit_fl (x : BitVec 64) : (if x &&& sb64 = 0#64 then 0#32 else 1#32) = fl x.msb := by
  by_cases h : x.msb <;> simp [fl, h, and_sb64]

theorem af_bit (v : BitVec 64) :
    ((v >>> 4 &&& 1#64).setWidth 32) = fl (v.getLsbD 4) := by
  unfold fl
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases h0 : i = 0
  · subst h0; by_cases h : v[4] = true <;> simp [h]
  · by_cases h : v[4] = true <;> simp [h, h0, BitVec.getLsbD_one]

/-- The parity of a byte, as `Silmaril.X86.parity` computes it. -/
def parity8 (x : BitVec 8) : Bool :=
  !(x.getLsbD 0 ^^ x.getLsbD 1 ^^ x.getLsbD 2 ^^ x.getLsbD 3 ^^
    x.getLsbD 4 ^^ x.getLsbD 5 ^^ x.getLsbD 6 ^^ x.getLsbD 7)

theorem par8 : ∀ x : BitVec 8,
    (((x.setWidth 32).cpop &&& 1#32 = 0#32) ↔ parity8 x = true) := by decide

theorem h255 : ∀ i : Fin 32, (255#32)[i.val] = decide (i.val < 8) := by decide

theorem low8 (r : BitVec 64) : r.setWidth 32 &&& 255#32 = (r.setWidth 8).setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases h8 : i < 8
  · simp [BitVec.getLsbD_and, BitVec.getLsbD_setWidth, h8, hi]
    intro _; have := h255 ⟨i, hi⟩; simp at this; rw [this]; simp [h8]
  · simp [BitVec.getLsbD_and, BitVec.getLsbD_setWidth, h8, hi]
    intro _; have := h255 ⟨i, hi⟩; simp at this; rw [this]; simp [h8]

theorem parity_low (r : BitVec 64) : parity r = parity8 (r.setWidth 8) := by
  simp [parity, parity8, BitVec.getLsbD_setWidth]

/-- The simulator's PF is x86's. -/
theorem par_eq (r : BitVec 64) : par r = fl (parity r) := by
  unfold par fl
  rw [low8, parity_low]
  by_cases h : parity8 (r.setWidth 8) = true
  · simp [h, (par8 _).2 h]
  · simp [h, mt (par8 _).1 h]

theorem zf_eq (r : BitVec 64) : zfOf r = fl (isZero r) := by
  by_cases h : r = 0#64 <;> simp [zfOf, fl, isZero, h]

theorem sf_eq (r : BitVec 64) : sfOf r = fl (sign r) := by
  simp only [sfOf, sign, sbit_fl]

/-- **ADD**: the simulator's flags are `Silmaril.X86.addFlags`. -/
theorem aluFlags_add (a b : BitVec 64) : aluFlags 0 a b = bitsOf (Silmaril.X86.addFlags a b) := by
  simp only [aluFlags, aluRes, bitsOf, Silmaril.X86.addFlags, Option.getD_some, ite_true]
  refine Prod.ext ?_ (Prod.ext (par_eq _) (Prod.ext ?_ (Prod.ext (zf_eq _) (Prod.ext (sf_eq _) ?_))))
  · simp only [fl, Silmaril.X86.addCarry_eq_spec, BitVec.toNat_add]
    have ha := a.isLt; have hb := b.isLt
    by_cases h : 2 ^ 64 ≤ a.toNat + b.toNat
    · rw [ite_eq_left (by omega)]; simp; omega
    · rw [ite_eq_right (by omega)]; simp; omega
  · exact af_bit _
  · exact sbit_fl _

/-- **SUB / CMP**: the simulator's flags are `Silmaril.X86.subFlags`. -/
theorem aluFlags_sub (op : Nat) (hop : op = 5 ∨ op = 7) (a b : BitVec 64) :
    aluFlags op a b = bitsOf (Silmaril.X86.subFlags a b) := by
  have h0 : op ≠ 0 := by omega
  simp only [aluFlags, aluRes, bitsOf, Silmaril.X86.subFlags, Option.getD_some, h0, ite_false]
  refine Prod.ext ?_ (Prod.ext (par_eq _) (Prod.ext ?_ (Prod.ext (zf_eq _) (Prod.ext (sf_eq _) ?_))))
  · simp only [fl, Silmaril.X86.subBorrow_eq_spec]; by_cases h : a.toNat < b.toNat <;> simp [h]
  · exact af_bit _
  · exact sbit_fl _

theorem aluRes_add (a b : BitVec 64) : aluRes 0 a b = a + b := rfl

theorem aluRes_sub (op : Nat) (hop : op = 5 ∨ op = 7) (a b : BitVec 64) : aluRes op a b = a - b := by
  have : op ≠ 0 := by omega
  simp [aluRes, this]

end Silmaril.Sim.X86Real
