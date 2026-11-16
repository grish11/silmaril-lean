module

public import Silmaril.Proofs.Sim.X86.GM.Sound

/-!
# GM: the width-generic forms

Narrow loads (`movzx`/`movsx` 8/16, `mov r32, [m]`, `movsxd`), compare and test at 8, 32 and
64 bits with register, immediate or memory operands, `op r64, [m]`, and `nop`
(`Silmaril.Sim.X86.GM.formOf`):

* `up v`: a `w`-bit value in the top bits of a 64-bit word. The 64-bit flag formulas of
  `up x, up y` are the `w`-bit flags of `x, y` (**`flagsN_up`**), so one flag code serves every
  width; `up_sshr`, `up_shr`: sign and zero extension back.
* **`opd_pure`**: an operand's code pushes `up` of the value `Ext.exec` reads (memory operands:
  in the window, `exec_loadK`); **`opd_holds`**: if it evaluates, its access is in the window.
* **`form_exec`**: `Ext.exec` of an instruction with a form is the form's semantics `formSem`.
* **`emitForm_sound`**, **`emitForm_holds`**, **`emitForm_progress`**.
-/

@[expose] public section

namespace Silmaril.Sim.X86.GM

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.X86 (Reg Word State AluOp)
open Silmaril.X86.Ext (Sz RM Mem Base Index Result retire readRM writeRM aluStep subFlagsN
  addFlagsN logicFlagsN isZeroN subBorrowN subOverflowN addCarryN addOverflowN)
open Silmaril.Sim.X86.G
open Silmaril.Wasm.Logic.Core (exec exec1 exec_cons exec_nil exec_append)

variable {H : Type} {s : Store H} {f : Frame} {σ : State}

/-! ## Narrow values in the top bits -/

/-- `v` in the top `w` bits of a 64-bit word. -/
def up {w : Nat} (v : BitVec w) : BitVec 64 := v.setWidth 64 <<< (64 - w)

section Up
variable {w : Nat}

theorem up_toNat (hw : w ≤ 64) (v : BitVec w) : (up v).toNat = v.toNat * 2 ^ (64 - w) := by
  have := v.isLt
  simp only [up, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by omega) hw))]
  apply Nat.mod_eq_of_lt
  calc v.toNat * 2 ^ (64 - w) < 2 ^ w * 2 ^ (64 - w) :=
        Nat.mul_lt_mul_of_pos_right this (Nat.two_pow_pos _)
    _ = 2 ^ 64 := by rw [← Nat.pow_add]; congr 1; omega

theorem up_add (hw : w ≤ 64) (x y : BitVec w) : up (x + y) = up x + up y := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, up_toNat hw, up_toNat hw, up_toNat hw, BitVec.toNat_add]
  have h : 2 ^ 64 = 2 ^ w * 2 ^ (64 - w) := by rw [← Nat.pow_add]; congr 1; omega
  rw [h, ← Nat.add_mul, Nat.mul_mod_mul_right]

theorem up_sub (hw : w ≤ 64) (x y : BitVec w) : up (x - y) = up x - up y := by
  have : x = (x - y) + y := by simp
  conv => rhs; rw [this, up_add hw]
  simp

theorem getLsbD_up (hw : 0 < w) (hw' : w ≤ 64) (v : BitVec w) :
    (up v).getLsbD 63 = v.getLsbD (w - 1) := by
  simp only [up, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  rw [show 63 - (64 - w) = w - 1 by omega]
  simp [show ¬ 63 < 64 - w by omega, show w - 1 < 64 by omega]

theorem msb_up (hw : 0 < w) (hw' : w ≤ 64) (v : BitVec w) : (up v).msb = v.msb := by
  rw [BitVec.msb_eq_getLsbD_last, BitVec.msb_eq_getLsbD_last, getLsbD_up hw hw']

theorem up_and (x y : BitVec w) : up (x &&& y) = up x &&& up y := by
  simp [up, BitVec.setWidth_and, BitVec.shiftLeft_and_distrib]
theorem up_or (x y : BitVec w) : up (x ||| y) = up x ||| up y := by
  simp [up, BitVec.setWidth_or, BitVec.shiftLeft_or_distrib]
theorem up_xor (x y : BitVec w) : up (x ^^^ y) = up x ^^^ up y := by
  simp [up, BitVec.setWidth_xor, BitVec.shiftLeft_xor_distrib]

theorem isZero_up (hw : w ≤ 64) (v : BitVec w) : isZeroN (up v) = isZeroN v := by
  simp only [isZeroN]
  have h1 := up_toNat hw v
  have h2 := Nat.two_pow_pos (64 - w)
  by_cases h : v = 0#w
  · subst h; simp [up]
  · have : v.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
    have : (up v).toNat ≠ 0 := by rw [h1]; exact Nat.mul_ne_zero this (by omega)
    have hu : up v ≠ 0#64 := fun e => this (by rw [e]; rfl)
    simp [h, hu]

/-- The modelled flags agree. -/
def FAgree (a b : Silmaril.X86.Flags) : Prop :=
  a.carry = b.carry ∧ a.zero = b.zero ∧ a.sign = b.sign ∧ a.overflow = b.overflow

/-- **The 64-bit flags of the operands in the top bits are the `w`-bit flags.** -/
theorem flagsN_up (hw : 0 < w) (hw' : w ≤ 64) (op : AluOp) (x y : BitVec w) :
    FAgree (Silmaril.X86.Ext.AluOp.flagsN op (up x) (up y))
      (Silmaril.X86.Ext.AluOp.flagsN op x y) := by
  have hm := msb_up hw hw'
  have hz := isZero_up hw'
  cases op <;> simp only [FAgree, Silmaril.X86.Ext.AluOp.flagsN, subFlagsN, addFlagsN,
    logicFlagsN, ← up_sub hw', ← up_add hw', ← up_and, ← up_or, ← up_xor, hm, hz, subBorrowN,
    subOverflowN, addCarryN, addOverflowN, and_self, and_true] <;>
    simp only [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_and, BitVec.getLsbD_or,
      BitVec.getLsbD_xor, BitVec.getLsbD_not, show 64 - 1 = 63 from rfl, getLsbD_up hw hw'] <;>
    simp [show w - 1 < w by omega]

theorem shl_up (hw : w ≤ 64) (v : BitVec 64) : v <<< (64 - w) = up (v.setWidth w) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [up, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  by_cases h : i < 64 - w
  · simp [h]
  · simp only [h, decide_false, Bool.not_false, Bool.true_and, hi, decide_true]
    rw [show decide (i - (64 - w) < w) = true from decide_eq_true (by omega)]
    rw [show decide (i - (64 - w) < 64) = true from decide_eq_true (by omega)]
    simp

theorem up_shr (hw : w ≤ 64) (x : BitVec w) : up x >>> (64 - w) = x.setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, up_toNat hw, Nat.shiftRight_eq_div_pow,
    Nat.mul_div_cancel _ (Nat.two_pow_pos _), BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by omega) hw))]

theorem up_sshr (hw : 0 < w) (hw' : w ≤ 64) (x : BitVec w) :
    (up x).sshiftRight (64 - w) = x.signExtend 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_sshiftRight, BitVec.getLsbD_signExtend, hi, decide_true,
    Bool.true_and]
  by_cases h : i < w
  · simp [h, up, show 64 - w + i < 64 by omega, show ¬ 64 - w + i < 64 - w by omega,
      show 64 - w + i - (64 - w) = i by omega]
    intro; omega
  · simp [h, show ¬ 64 - w + i < 64 by omega, show ¬ 64 ≤ i by omega, msb_up hw hw']

theorem up_64 (x : BitVec 64) : up x = x := by simp [up]

end Up

theorem mask32 (e : BitVec 64) : e &&& 0xffffffff#64 = (e.setWidth 32).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_setWidth]
  rw [show (0xffffffff#64) = BitVec.ofNat 64 (2 ^ 32 - 1) from rfl, BitVec.getLsbD_ofNat,
    Nat.testBit_two_pow_sub_one]
  by_cases h : i < 32 <;> simp [h, hi]

/-! ## Operand and flag code -/

/-- The widths of the forms. -/
def WOk (w : Nat) : Prop := w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64

theorem WOk.pos {w : Nat} (h : WOk w) : 0 < w := by rcases h with rfl | rfl | rfl | rfl <;> decide
theorem WOk.le {w : Nat} (h : WOk w) : w ≤ 64 := by rcases h with rfl | rfl | rfl | rfl <;> decide

theorem pure_shl {X : List Instr} {x : Word} (hX : Pure s f X x) {w : Nat} (hw : WOk w) :
    Pure s f (upCode w X) (up (x.setWidth w)) := by
  have hk : (BitVec.ofNat 64 (64 - w)).toNat % 64 = 64 - w := by
    rcases hw with rfl | rfl | rfl | rfl <;> rfl
  have := hX.op (pure_c64 (BitVec.ofNat 64 (64 - w))) .shl (z := x <<< (64 - w)) (by
    simp only [intBinOp, IntType.width, hk]; rfl)
  rw [shl_up hw.le] at this
  simpa [upCode, List.append_assoc] using this

/-- The value of an operand `Ext.exec` reads. -/
def opdRead (w : Nat) (o : Opd) (σ : State) (mem : Silmaril.Process.Memory) (next : Word) :
    Option (BitVec w) :=
  match o with
  | .reg r => some ((σ.read r).setWidth w)
  | .imm c => some (c.setWidth w)
  | .mem m _ => (Silmaril.X86.Ext.loadN mem (m.addr σ next) (w / 8)).map (·.setWidth w)

@[simp] theorem opdRead_reg (w : Nat) (r : Reg) (σ : State) (mem : Silmaril.Process.Memory)
    (next : Word) : opdRead w (.reg r) σ mem next = some ((σ.read r).setWidth w) := rfl
@[simp] theorem opdRead_imm (w : Nat) (c : Word) (σ : State) (mem : Silmaril.Process.Memory)
    (next : Word) : opdRead w (.imm c) σ mem next = some (c.setWidth w) := rfl

theorem wdiv {w : Nat} (hw : WOk w) : w / 8 = 1 ∨ w / 8 = 2 ∨ w / 8 = 4 ∨ w / 8 = 8 := by
  rcases hw with rfl | rfl | rfl | rfl <;> simp

/-- **An operand's code pushes the value `Ext.exec` reads**, in the top bits. -/
theorem opd_pure (hE : Enc s f σ) {mem : Silmaril.Process.Memory} {W : Win}
    (hM : MemEnc s f mem W) {w : Nat} (hw : WOk w) (o : Opd) (next : Word)
    (hacc : ∀ a k, o.access w σ next = some (a, k) → W.HoldsK k a) :
    ∃ x, opdRead w o σ mem next = some x ∧ Pure s f (upCode w (opdCode W w o)) (up x) := by
  cases o with
  | reg r => exact ⟨_, rfl, pure_shl (pure_gget (hE.2.1 r)) hw⟩
  | imm c => exact ⟨_, rfl, pure_shl (pure_c64 c) hw⟩
  | mem m hp =>
    obtain ⟨L, hL, hP⟩ := exec_loadK hM (wdiv hw) (pure_addr hE hp next) (hacc _ _ rfl)
    refine ⟨(BitVec.ofNat 64 L).setWidth w, by simp only [opdRead, hL, Option.map_some], ?_⟩
    have := pure_shl hP hw
    have he : ((BitVec.ofNat (8 * (w / 8)) L).setWidth 64).setWidth w =
        (BitVec.ofNat 64 L).setWidth w := by
      apply BitVec.eq_of_toNat_eq
      rcases hw with rfl | rfl | rfl | rfl <;> simp
    rw [he] at this
    exact this

/-- If an operand's code evaluates, its access is in the window. -/
theorem opd_holds (hE : Enc s f σ) {mem : Silmaril.Process.Memory} {W : Win}
    (hM : MemEnc s f mem W) {w : Nat} (hw : WOk w) (o : Opd) (next : Word) {rs : List Val}
    {rest : List Instr} {r : Store H × Frame × List Val}
    (he : exec s f rs (upCode w (opdCode W w o) ++ rest) = some r) :
    ∀ a k, o.access w σ next = some (a, k) → W.HoldsK k a := by
  intro a k ha
  cases o with
  | reg r => cases ha
  | imm c => cases ha
  | mem m hp =>
    obtain ⟨B, -, -, h32, hlim, -⟩ := id hM
    simp only [Opd.access, Option.some.injEq, Prod.mk.injEq] at ha
    obtain ⟨rfl, rfl⟩ := ha
    obtain ⟨r₁, h₁⟩ := exec_append_some he
    obtain ⟨r₂, h₂⟩ := exec_append_some h₁
    have hk : 0 < w / 8 := by rcases wdiv hw with h | h | h | h <;> omega
    exact loadK_holds hk (pure_addr hE hp next) h32 hlim h₂

/-- **The flag code**: it pushes SF, ZF, OF, CF encoding the flags of `op x, y`. -/
theorem exec_flagPush {X Y : List Instr} {x y : Word} (hX : Pure s f X x) (hY : Pure s f Y y)
    (op : AluOp) (rs : List Val) : ∃ c o z g,
      exec s f rs (flagPush op X Y) =
        some (s, f, Val.i64 c :: Val.i64 o :: Val.i64 z :: Val.i64 g :: rs) ∧
      FlagEnc (some (Val.i64 c)) (Silmaril.X86.Ext.AluOp.flagsN op x y).carry ∧
      FlagEnc (some (Val.i64 o)) (Silmaril.X86.Ext.AluOp.flagsN op x y).overflow ∧
      FlagEnc (some (Val.i64 z)) (Silmaril.X86.Ext.AluOp.flagsN op x y).zero ∧
      FlagEnc (some (Val.i64 g)) (Silmaril.X86.Ext.AluOp.flagsN op x y).sign := by
  have hX' : ∀ rs, exec s f rs X = some (s, f, Val.i64 x :: rs) := hX
  have hY' : ∀ rs, exec s f rs Y = some (s, f, Val.i64 y :: rs) := hY
  cases op <;>
  · simp only [flagPush, carryCode, overflowCode, zeroCode, msbCode, notCode, aluWasm,
      List.append_assoc, List.cons_append, List.nil_append, exec_append, exec_cons, exec_nil,
      hX', hY', exec1_c64, exec1_add, exec1_sub, exec1_and, exec1_or, exec1_xor, exec1_shr63,
      xor_neg_one]
    first
    | exact ⟨_, _, _, _, rfl, flagEnc_msb _, flagEnc_msb _, flagEnc_zero _, flagEnc_msb _⟩
    | exact ⟨_, _, _, _, rfl, flagEnc_false, flagEnc_false, flagEnc_zero _, flagEnc_msb _⟩

theorem exec_flagSet (hl : Layout s f) (c o z g : BitVec 64) (rs : List Val) :
    exec s f (Val.i64 c :: Val.i64 o :: Val.i64 z :: Val.i64 g :: rs) flagSet =
      some (upd (upd (upd (upd s f .cf (Val.i64 c)) f .of (Val.i64 o)) f .zf (Val.i64 z)) f .sf
        (Val.i64 g), f, rs) := by
  simp (maxDischargeDepth := 20) only [flagSet, exec_cons, exec_nil, exec1_gset, hl, Layout.upd]

/-! ## Form semantics -/

/-- The state after a flag form on operand values `x`, `y` (RIP not advanced). -/
def flagSem (F : FForm) (x y : BitVec F.w) (σ : State) : State :=
  { (match F.wb with
      | none => σ
      | some d => σ.write d ((Silmaril.X86.Ext.AluOp.resultN F.op x y).setWidth 64)) with
    flags := Silmaril.X86.Ext.AluOp.flagsN F.op x y }

/-- The value a load form writes. -/
def loadVal (L : LForm) (x : BitVec L.w) : Word :=
  if L.dsz = .d then
    ((if L.sx then x.signExtend 64 else x.setWidth 64).setWidth 32).setWidth 64
  else if L.sx then x.signExtend 64 else x.setWidth 64

/-- **The semantics of a form** (RIP not advanced). -/
def formSem : Form → State → Silmaril.Process.Memory → Word →
    Option (State × Silmaril.Process.Memory)
  | .flag F, σ, mem, next => (opdRead F.w F.a σ mem next).bind fun x =>
      (opdRead F.w F.b σ mem next).map fun y => (flagSem F x y σ, mem)
  | .load L, σ, mem, next =>
      (opdRead L.w L.src σ mem next).map fun x => (σ.write L.d (loadVal L x), mem)
  | .nop, σ, mem, _ => some (σ, mem)

/-- A memory operand. -/
def Opd.isMem : Opd → Bool
  | .mem _ _ => true
  | _ => false

theorem Opd.access_none {o : Opd} (h : o.isMem = false) (w : Nat) (σ : State) (next : Word) :
    o.access w σ next = none := by
  cases o <;> first | rfl | cases h

/-- The forms the methods handle: widths 8–64, at most one memory operand, write-back at 64
bits. -/
def Form.Ok : Form → Prop
  | .flag F => WOk F.w ∧ (F.a.isMem && F.b.isMem) = false ∧ (∀ d, F.wb = some d → F.w = 64)
  | .load L => WOk L.w
  | .nop => True

theorem WOk.shift {w : Nat} (hw : WOk w) : (BitVec.ofNat 64 (64 - w)).toNat % 64 = 64 - w := by
  rcases hw with rfl | rfl | rfl | rfl <;> rfl

/-- The shift down of a load form: the operand's top bits, zero- or sign-extended. -/
theorem pure_loadShr {X : List Instr} {w : Nat} {x : BitVec w} (hP : Pure s f X (up x))
    (hw : WOk w) (sx : Bool) :
    Pure s f (X ++ [c64 (BitVec.ofNat 64 (64 - w)), b64op (.shr (if sx then .signed else .unsigned))])
      (if sx then x.signExtend 64 else x.setWidth 64) := by
  have hk : (BitVec.ofNat 64 (64 - w)).toNat % 64 = 64 - w := hw.shift
  have hS : Pure s f (X ++ [c64 (BitVec.ofNat 64 (64 - w))] ++
      [b64op (.shr (if sx then .signed else .unsigned))])
      (if sx then x.signExtend 64 else x.setWidth 64) :=
    hP.op (pure_c64 (BitVec.ofNat 64 (64 - w))) (.shr (if sx then .signed else .unsigned)) (by
      cases sx
      · simp only [intBinOp, IntType.width, hk, Bool.false_eq_true, ite_false]
        rw [← up_shr hw.le]; rfl
      · simp only [intBinOp, IntType.width, hk, ite_true]
        rw [← up_sshr hw.pos hw.le])
  simpa [List.append_assoc] using hS

/-- The 32-bit mask of a load form. -/
theorem pure_loadMask {X : List Instr} {v : Word} (hS : Pure s f X v) :
    Pure s f (X ++ [c64 0xffffffff, b64op .and]) ((v.setWidth 32).setWidth 64) := by
  have hM : Pure s f (X ++ [c64 0xffffffff] ++ [b64op .and]) ((v.setWidth 32).setWidth 64) :=
    hS.op (pure_c64 0xffffffff) .and (by simp only [intBinOp]; rw [← mask32]; rfl)
  simpa [List.append_assoc] using hM

/-- The Wasm side of a load form. -/
theorem form_wasm_load (hE : Enc s f σ) {mem : Silmaril.Process.Memory} {W : Win}
    (hM : MemEnc s f mem W) {L : LForm} (hw : WOk L.w) (next : Word)
    (hacc : ∀ a k, (Form.load L).access σ next = some (a, k) → W.HoldsK k a) :
    ∃ σ₁, formSem (.load L) σ mem next = some (σ₁, mem) ∧ σ₁.rip = σ.rip ∧
      ∃ s', exec s f [] ((Form.load L).code W) = some (s', f, []) ∧ Enc s' f σ₁ ∧
        wbytes s' f = wbytes s f := by
  obtain ⟨w, sx, src, dsz, d⟩ := L
  obtain ⟨x, hx, hP⟩ := opd_pure hE hM hw src next hacc
  have hV : Pure s f (upCode w (opdCode W w src) ++
      [c64 (BitVec.ofNat 64 (64 - w)), b64op (.shr (if sx then .signed else .unsigned))] ++
      (if dsz = .d then [c64 0xffffffff, b64op .and] else []))
      (loadVal ⟨w, sx, src, dsz, d⟩ x) := by
    cases dsz
    · simpa [loadVal] using pure_loadMask (pure_loadShr hP hw sx)
    · simpa [loadVal] using pure_loadShr hP hw sx
  obtain ⟨h1, hE1, hw1⟩ := tail_reg hE [] d (loadVal ⟨w, sx, src, dsz, d⟩ x)
  refine ⟨σ.write d (loadVal ⟨w, sx, src, dsz, d⟩ x), by simp only [formSem, hx, Option.map_some],
    rfl, _, ?_, hE1, hw1⟩
  simp only [Form.code]
  rw [exec_append, hV []]
  exact h1

/-- The accesses of the operands of a flag form with at most one memory operand. -/
theorem flag_acc {W : Win} {next : Word} {w : Nat} {op : AluOp} {a b : Opd} {wb : Option Reg}
    (hab : (a.isMem && b.isMem) = false)
    (hacc : ∀ a' k, (Form.flag ⟨w, op, a, b, wb⟩).access σ next = some (a', k) → W.HoldsK k a') :
    (∀ a' k, a.access w σ next = some (a', k) → W.HoldsK k a') ∧
      (∀ a' k, b.access w σ next = some (a', k) → W.HoldsK k a') := by
  refine ⟨fun a' k h' => hacc a' k (by simp only [Form.access, h']), fun a' k h' => ?_⟩
  cases hm : a.isMem
  · exact hacc a' k (by simp only [Form.access, Opd.access_none hm, h'])
  · have hb : b.isMem = false := by simpa [hm] using hab
    exact nomatch (Opd.access_none hb w σ next).symm.trans h'

/-- The Wasm side of a flag form. -/
theorem form_wasm_flag (hE : Enc s f σ) {mem : Silmaril.Process.Memory} {W : Win}
    (hM : MemEnc s f mem W) {F : FForm} (hF : (Form.flag F).Ok) (next : Word)
    (hacc : ∀ a k, (Form.flag F).access σ next = some (a, k) → W.HoldsK k a) :
    ∃ σ₁, formSem (.flag F) σ mem next = some (σ₁, mem) ∧ σ₁.rip = σ.rip ∧
      ∃ s', exec s f [] ((Form.flag F).code W) = some (s', f, []) ∧ Enc s' f σ₁ ∧
        wbytes s' f = wbytes s f := by
  obtain ⟨w, op, a, b, wb⟩ := F
  obtain ⟨hw, hab, hwb⟩ := hF
  obtain ⟨ha, hb⟩ := flag_acc hab hacc
  obtain ⟨x, hx, hX⟩ := opd_pure hE hM hw a next ha
  obtain ⟨y, hy, hY⟩ := opd_pure hE hM hw b next hb
  obtain ⟨c, o, z, g, hfp, hc, ho, hz, hg⟩ := exec_flagPush hX hY op []
  obtain ⟨ec, ez, es, eo⟩ := flagsN_up hw.pos hw.le op x y
  have hc' : FlagEnc (some (Val.i64 c)) (Silmaril.X86.Ext.AluOp.flagsN op x y).carry := ec ▸ hc
  have ho' : FlagEnc (some (Val.i64 o)) (Silmaril.X86.Ext.AluOp.flagsN op x y).overflow := eo ▸ ho
  have hz' : FlagEnc (some (Val.i64 z)) (Silmaril.X86.Ext.AluOp.flagsN op x y).zero := ez ▸ hz
  have hg' : FlagEnc (some (Val.i64 g)) (Silmaril.X86.Ext.AluOp.flagsN op x y).sign := es ▸ hg
  refine ⟨flagSem ⟨w, op, a, b, wb⟩ x y σ, by simp only [formSem, hx, hy, Option.bind_some,
    Option.map_some], by simp only [flagSem]; split <;> rfl, ?_⟩
  cases wb with
  | none =>
    refine ⟨_, ?_, enc_flags hE c o z g _ (regsAfter_same _ _ rfl) rfl hc' ho' hz' hg', ?_⟩
    · simp only [Form.code, wbCode, List.append_nil]
      rw [exec_append, hfp]
      exact exec_flagSet hE.1 c o z g []
    · simp only [wbytes_upd]
  | some d =>
    show ∃ s', exec s f [] ((Form.flag ⟨w, op, a, b, some d⟩).code W) = some (s', f, []) ∧
      Enc s' f (flagSem ⟨w, op, a, b, some d⟩ x y σ) ∧ wbytes s' f = wbytes s f
    obtain rfl : w = 64 := hwb d rfl
    have hR : Pure s f (upCode 64 (opdCode W 64 a) ++ upCode 64 (opdCode W 64 b) ++
        [b64op (aluWasm op)]) ((Silmaril.X86.Ext.AluOp.resultN op x y).setWidth 64) :=
      (up_64 x ▸ hX).op (up_64 y ▸ hY) (aluWasm op) (by cases op <;> rfl)
    obtain ⟨h1, hE1, hw1⟩ := tail_reg hE [Val.i64 c, Val.i64 o, Val.i64 z, Val.i64 g] d
      ((Silmaril.X86.Ext.AluOp.resultN op x y).setWidth 64)
    have hwb' : exec s f [Val.i64 c, Val.i64 o, Val.i64 z, Val.i64 g]
        (upCode 64 (opdCode W 64 a) ++ upCode 64 (opdCode W 64 b) ++
          [b64op (aluWasm op), gset (.reg d)]) =
        some (upd s f (.reg d) (Val.i64 ((Silmaril.X86.Ext.AluOp.resultN op x y).setWidth 64)), f,
          [Val.i64 c, Val.i64 o, Val.i64 z, Val.i64 g]) := by
      have hsplit : upCode 64 (opdCode W 64 a) ++ upCode 64 (opdCode W 64 b) ++
          [b64op (aluWasm op), gset (.reg d)] = (upCode 64 (opdCode W 64 a) ++
          upCode 64 (opdCode W 64 b) ++ [b64op (aluWasm op)]) ++ [gset (.reg d)] := by simp
      rw [hsplit, exec_append, hR]
      simp only
      exact h1
    refine ⟨_, ?_, enc_flags hE1 c o z g _ (regsAfter_same _ _ rfl) rfl hc' ho' hz' hg', ?_⟩
    · simp only [Form.code, wbCode]
      rw [exec_append, exec_append, hfp]
      simp only
      rw [hwb']
      exact exec_flagSet hE1.1 c o z g []
    · simp only [wbytes_upd, hw1]

/-- **The Wasm side of a form**: with its access in the window, the form's semantics is defined
and its code evaluates to a store encoding the result, the Wasm memory unchanged. -/
theorem form_wasm (hE : Enc s f σ) {mem : Silmaril.Process.Memory} {W : Win}
    (hM : MemEnc s f mem W) {F : Form} (hF : F.Ok) (next : Word)
    (hacc : ∀ a k, F.access σ next = some (a, k) → W.HoldsK k a) :
    ∃ σ₁, formSem F σ mem next = some (σ₁, mem) ∧ σ₁.rip = σ.rip ∧
      ∃ s', exec s f [] (F.code W) = some (s', f, []) ∧ Enc s' f σ₁ ∧
        wbytes s' f = wbytes s f := by
  cases F with
  | nop => exact ⟨σ, rfl, rfl, s, rfl, hE, rfl⟩
  | load L => exact form_wasm_load hE hM hF next hacc
  | flag F => exact form_wasm_flag hE hM hF next hacc

/-! ## The x86 side -/

theorem trunc_ext {v : Nat} (imm : BitVec v) {w : Nat} (hw : w ≤ 64) :
    (imm.setWidth 64).setWidth w = imm.setWidth w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth]
  simp [show i < 64 by omega]

theorem trunc_sext {v : Nat} (imm : BitVec v) {w : Nat} (hw : w ≤ 64) :
    (imm.signExtend 64).setWidth w = imm.signExtend w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend]
  simp [show i < 64 by omega, hi]

theorem sz_le (sz : Sz) : sz.bits ≤ 64 := by cases sz <;> decide

theorem zeroExt32 {w : Nat} (hw : w ≤ 32) (v : BitVec w) :
    BitVec.setWidth 64 (BitVec.setWidth 32 v) =
      BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 v)) := by
  apply BitVec.eq_of_toNat_eq
  have := Nat.lt_of_lt_of_le v.isLt (Nat.pow_le_pow_right (by omega) hw)
  simp only [BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (by omega : v.toNat < 2 ^ 64)]

theorem signExt32 {w : Nat} (_hw : w ≤ 32) (v : BitVec w) :
    BitVec.setWidth 64 (BitVec.signExtend 32 v) =
      BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.signExtend 64 v)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend]
  by_cases h : i < 32 <;> simp [h, show i < 64 by omega]

theorem readRM_opd {dst : RM} {o : Opd} (h : opdOf dst = some o) (sz : Sz) (σ : State)
    (mem : Silmaril.Process.Memory) (next : Word) :
    readRM sz dst σ mem next = opdRead sz.bits o σ mem next := by
  cases dst with
  | reg r => cases h; rfl
  | mem m =>
    simp only [opdOf] at h
    split at h
    · cases h; cases sz <;> rfl
    · cases h

theorem readNarrow_opd {dst : RM} {o : Opd} (h : opdOf dst = some o) (n : Silmaril.X86.Ext.Narrow)
    (σ : State) (mem : Silmaril.Process.Memory) (next : Word) :
    Silmaril.X86.Ext.readNarrow n dst σ mem next = opdRead n.bits o σ mem next := by
  cases dst with
  | reg r => cases h; rfl
  | mem m =>
    simp only [opdOf] at h
    split at h
    · cases h; cases n <;> rfl
    · cases h

/-- `Ext.exec` of `i` is the semantics of its form (RIP advanced by `retire`). -/
def FormExec (i : Silmaril.X86.Ext.Instr) : Prop :=
  ∀ {F : Form}, formOf i = some F → ∀ (σ : State) (mem : Silmaril.Process.Memory) (len : Nat),
    Silmaril.X86.Ext.exec i σ mem len =
      retire (σ.rip + BitVec.ofNat 64 len) (formSem F σ mem (σ.rip + BitVec.ofNat 64 len))

theorem formExec_load {sz d m} : FormExec (.load sz d m) := by
  intro F h σ mem len
  have h' : load32Of sz d m = some F := h
  unfold load32Of at h'
  split at h'
  · rename_i hp
    cases h'
    obtain ⟨rfl, -⟩ := hp
    simp only [Silmaril.X86.Ext.exec, readRM, formSem, opdRead, Option.map_map]
    rfl
  · cases h'

theorem formExec_movx {sx sz n d src} : FormExec (.movx sx sz n d src) := by
  intro F h σ mem len
  obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp h
  simp only [Silmaril.X86.Ext.exec, readNarrow_opd ho, formSem]
  cases opdRead n.bits o σ mem (σ.rip + BitVec.ofNat 64 len) with
  | none => rfl
  | some v =>
    simp only [Option.map_some]
    congr 3
    cases sz
    · simp only [loadVal, ite_true, Sz.write]
      congr 1
      cases sx
      · simp only [Bool.false_eq_true, ite_false]
        exact zeroExt32 (by cases n <;> decide) v
      · simp only [ite_true]
        exact signExt32 (by cases n <;> decide) v
    · simp only [loadVal, reduceCtorEq, ite_false]
      cases sx <;> rfl

theorem formExec_movsxd {d src} : FormExec (.movsxd d src) := by
  intro F h σ mem len
  obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp h
  simp only [Silmaril.X86.Ext.exec, readRM_opd ho, formSem, loadVal]
  rfl

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
/-- The forms with literal operands. -/
theorem formExec_lit : (∀ imm, FormExec (.testA8 imm)) ∧ (∀ imm, FormExec (.cmpA8 imm)) ∧
    (∀ sz imm, FormExec (.testA sz imm)) ∧ (∀ n, FormExec (.nop n)) := by
  refine ⟨fun _ => ?_, fun _ => ?_, fun _ _ => ?_, fun _ => ?_⟩ <;> intro F h σ mem len <;>
    cases h
  all_goals first
    | rfl
    | (simp (disch := first | decide | exact sz_le _) only [Silmaril.X86.Ext.exec, formSem,
         opdRead_reg, opdRead_imm, Option.map_some, Option.bind_some, trunc_ext, trunc_sext,
         BitVec.setWidth_eq]
       try rfl
       done)

set_option linter.unusedSimpArgs false in
/-- The flag forms of `test` and the 8-bit `cmp`. -/
theorem formExec_flagOf : (∀ sz dst src, FormExec (.test sz dst src)) ∧
    (∀ dst src, FormExec (.test8 dst src)) ∧ (∀ dst imm, FormExec (.testI8 dst imm)) ∧
    (∀ dst imm, FormExec (.cmpI8 dst imm)) := by
  refine ⟨fun _ _ _ => ?_, fun _ _ => ?_, fun _ _ => ?_, fun _ _ => ?_⟩ <;>
  · intro F h σ mem len
    simp only [formOf, flagOf] at h
    obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp h
    simp (disch := first | decide | exact sz_le _) only [Silmaril.X86.Ext.exec, readRM_opd ho,
      readNarrow_opd ho, formSem, opdRead_reg, opdRead_imm, Option.map_some, Option.bind_some,
      trunc_ext, trunc_sext, BitVec.setWidth_eq, Silmaril.X86.Ext.Narrow.bits]
    generalize opdRead _ o σ mem _ = r
    cases r <;> rfl

set_option linter.unusedSimpArgs false in
/-- The `cmp` forms of the ALU instructions. -/
theorem formExec_cmp : (∀ sz op imm, FormExec (.aluA sz op imm)) ∧
    (∀ sz op dst src, FormExec (.alu sz op dst src)) ∧
    (∀ sz op dst imm, FormExec (.aluI sz op dst imm)) ∧
    (∀ sz op dst imm, FormExec (.aluI8 sz op dst imm)) := by
  refine ⟨fun _ _ _ => ?_, fun _ _ _ _ => ?_, fun _ _ _ _ => ?_, fun _ _ _ _ => ?_⟩ <;>
  · intro F h σ mem len
    simp only [formOf, cmpIOf, cmpOf] at h
    split at h
    · rename_i hop
      subst hop
      simp only [flagOf] at h
      obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp h
      simp (disch := first | decide | exact sz_le _) only [Silmaril.X86.Ext.exec, aluStep,
        readRM_opd ho, formSem, opdRead_reg, opdRead_imm, Option.map_some, Option.bind_some,
        trunc_ext, trunc_sext, BitVec.setWidth_eq, Silmaril.X86.Ext.Narrow.bits]
      generalize opdRead _ o σ mem _ = r
      cases r <;> rfl
    · cases h

theorem formExec_aluR {sz op d src} : FormExec (.aluR sz op d src) := by
  intro F h σ mem len
  obtain ⟨o, ho, h⟩ := Option.bind_eq_some_iff.mp (show aluROf sz op d src = some F from h)
  simp only [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.aluStepR, readRM_opd ho]
  split at h
  · cases h
    rename_i hop
    subst hop
    simp only [formSem, opdRead_reg, Option.bind_some]
    generalize opdRead _ o σ mem _ = r
    cases r <;> rfl
  · split at h
    · cases h
      rename_i hop hq
      subst hq
      simp only [formSem, opdRead_reg, Option.bind_some, hop, ite_false, Sz.bits]
      generalize opdRead _ o σ mem _ = r
      cases r <;> rfl
    · cases h

/-- **`Ext.exec` of an instruction with a form is the form's semantics.** -/
theorem form_exec {i : Silmaril.X86.Ext.Instr} {F : Form} (h : formOf i = some F) (σ : State)
    (mem : Silmaril.Process.Memory) (len : Nat) :
    Silmaril.X86.Ext.exec i σ mem len =
      retire (σ.rip + BitVec.ofNat 64 len) (formSem F σ mem (σ.rip + BitVec.ofNat 64 len)) := by
  cases i with
  | load sz d m => exact formExec_load h σ mem len
  | movx sx sz n d src => exact formExec_movx h σ mem len
  | movsxd d src => exact formExec_movsxd h σ mem len
  | test sz dst src => exact formExec_flagOf.1 sz dst src h σ mem len
  | test8 dst src => exact formExec_flagOf.2.1 dst src h σ mem len
  | testI8 dst imm => exact formExec_flagOf.2.2.1 dst imm h σ mem len
  | cmpI8 dst imm => exact formExec_flagOf.2.2.2 dst imm h σ mem len
  | testA8 imm => exact formExec_lit.1 imm h σ mem len
  | cmpA8 imm => exact formExec_lit.2.1 imm h σ mem len
  | testA sz imm => exact formExec_lit.2.2.1 sz imm h σ mem len
  | nop n => exact formExec_lit.2.2.2 n h σ mem len
  | aluA sz op imm => exact formExec_cmp.1 sz op imm h σ mem len
  | alu sz op dst src => exact formExec_cmp.2.1 sz op dst src h σ mem len
  | aluI sz op dst imm => exact formExec_cmp.2.2.1 sz op dst imm h σ mem len
  | aluI8 sz op dst imm => exact formExec_cmp.2.2.2 sz op dst imm h σ mem len
  | aluR sz op d src => exact formExec_aluR h σ mem len
  | _ => cases h

theorem sz_wok (sz : Sz) : WOk sz.bits := by cases sz <;> simp [WOk, Sz.bits]
theorem n_wok (n : Silmaril.X86.Ext.Narrow) : WOk n.bits := by
  cases n <;> simp [WOk, Silmaril.X86.Ext.Narrow.bits]

theorem isMem_and_false (o : Opd) : (o.isMem && false) = false := by simp

theorem wok8 : WOk 8 := Or.inl rfl
theorem wok32 : WOk 32 := Or.inr (Or.inr (Or.inl rfl))
theorem wok64 : WOk 64 := Or.inr (Or.inr (Or.inr rfl))

theorem flagOf_ok {w : Nat} (hw : WOk w) {op : AluOp} {a : RM} {b : Opd} (hb : b.isMem = false)
    {F : Form} (h : flagOf w op a b = some F) : F.Ok := by
  obtain ⟨o, -, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨hw, by simp [hb], fun _ h => by cases h⟩

theorem cmpIOf_ok {sz : Sz} {op : AluOp} {a : RM} {c : Word} {F : Form}
    (h : cmpIOf sz op a c = some F) : F.Ok := by
  simp only [cmpIOf] at h
  split at h
  · exact flagOf_ok (sz_wok sz) rfl h
  · cases h

theorem load32Of_ok {sz : Sz} {d : Reg} {m : Mem} {F : Form} (h : load32Of sz d m = some F) :
    F.Ok := by
  unfold load32Of at h
  split at h
  · cases h; exact wok32
  · cases h

theorem loadOf_ok {w : Nat} (hw : WOk w) {sx : Bool} {sz : Sz} {d : Reg} {src : RM} {F : Form}
    (h : (opdOf src).map (fun o => Form.load ⟨w, sx, o, sz, d⟩) = some F) : F.Ok := by
  obtain ⟨o, -, rfl⟩ := Option.map_eq_some_iff.mp h
  exact hw

theorem cmpOf_ok {sz : Sz} {op : AluOp} {a : RM} {src : Reg} {F : Form}
    (h : cmpOf sz op a src = some F) : F.Ok := by
  simp only [cmpOf] at h
  split at h
  · exact flagOf_ok (sz_wok _) rfl h
  · cases h

theorem aluROf_ok {sz : Sz} {op : AluOp} {d : Reg} {src : RM} {F : Form}
    (h : aluROf sz op d src = some F) : F.Ok := by
  simp only [aluROf] at h
  obtain ⟨o, -, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · cases h; exact ⟨sz_wok _, rfl, fun _ h => by cases h⟩
  · split at h
    · cases h; exact ⟨wok64, rfl, fun _ h => by cases h; rfl⟩
    · cases h

/-- The forms of instructions are well formed. -/
theorem formOf_ok {i : Silmaril.X86.Ext.Instr} {F : Form} (h : formOf i = some F) : F.Ok := by
  cases i with
  | load sz d m => exact load32Of_ok h
  | movx sx sz n d src => exact loadOf_ok (n_wok n) h
  | movsxd d src => exact loadOf_ok wok32 h
  | test sz dst src => exact flagOf_ok (sz_wok _) rfl h
  | test8 dst src => exact flagOf_ok wok8 rfl h
  | testI8 dst imm => exact flagOf_ok wok8 rfl h
  | cmpI8 dst imm => exact flagOf_ok wok8 rfl h
  | testA8 imm => cases h; exact ⟨wok8, rfl, fun _ h => by cases h⟩
  | cmpA8 imm => cases h; exact ⟨wok8, rfl, fun _ h => by cases h⟩
  | testA sz imm => cases h; exact ⟨sz_wok _, rfl, fun _ h => by cases h⟩
  | aluA sz op imm => exact cmpIOf_ok h
  | alu sz op dst src => exact cmpOf_ok h
  | aluR sz op d src => exact aluROf_ok h
  | aluI sz op dst imm => exact cmpIOf_ok h
  | aluI8 sz op dst imm => exact cmpIOf_ok h
  | nop n => cases h; trivial
  | _ => cases h

/-- Instructions with a form are not memory or stack forms. -/
theorem accessMem_form {i : Silmaril.X86.Ext.Instr} {F : Form} (h : formOf i = some F)
    (σ : State) (len : Nat) : accessMem i σ len = none := by
  unfold formOf at h
  split at h
  all_goals try (cases h; done)
  all_goals try rfl
  rename_i sz d m
  simp only [load32Of] at h
  split at h
  · rename_i hp
    obtain ⟨rfl, -⟩ := hp
    rfl
  · cases h

theorem access_form {i : Silmaril.X86.Ext.Instr} {F : Form} (h : formOf i = some F)
    (σ : State) (len : Nat) :
    access i σ len = F.access σ (σ.rip + BitVec.ofNat 64 len) := by
  simp only [access, accessMem_form h, h, Option.bind_some]

/-- The defined modelled flags of a form's result. -/
theorem formSem_defined {F : Form} {σ σ₁ : State} {mem mem₁ : Silmaril.Process.Memory}
    {next : Word} (h : formSem F σ mem next = some (σ₁, mem₁)) (hd : Defined σ.flags) :
    Defined σ₁.flags ∧ mem₁ = mem := by
  cases F with
  | nop => cases h; exact ⟨hd, rfl⟩
  | load L =>
    simp only [formSem, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨x, -, rfl, rfl⟩ := h
    exact ⟨hd, rfl⟩
  | flag F =>
    simp only [formSem, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨x, -, y, -, rfl, rfl⟩ := h
    refine ⟨?_, rfl⟩
    simp only [flagSem]
    cases F.op <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- Operands in the window are read. -/
theorem opdRead_some {mem : Silmaril.Process.Memory} {W : Win} {s : Store H}
    (hM : MemEnc s f mem W) {w : Nat} (o : Opd) (σ : State) (next : Word)
    (hacc : ∀ a k, o.access w σ next = some (a, k) → W.HoldsK k a) :
    ∃ x, opdRead w o σ mem next = some x := by
  cases o with
  | reg r => exact ⟨_, rfl⟩
  | imm c => exact ⟨_, rfl⟩
  | mem m hp =>
    obtain ⟨B, L, -, hL, -⟩ := hM.loadK (hacc _ _ rfl)
    exact ⟨(BitVec.ofNat 64 L).setWidth w, by simp only [opdRead, hL, Option.map_some]⟩

/-- **Soundness of the form methods.** -/
theorem emitForm_sound {W : Win} {i : Silmaril.X86.Ext.Instr} {len : Nat} {code : List Instr}
    (hc : emitForm W i len = some code) (hE : Enc s f σ) {mem : Silmaril.Process.Memory}
    (hM : MemEnc s f mem W) {σ' : State} {mem' : Silmaril.Process.Memory}
    (hx : Silmaril.X86.Ext.exec i σ mem len = .ok σ' mem')
    (hw : ∀ a k, access i σ len = some (a, k) → W.HoldsK k a) :
    ∃ s', exec s f [] code = some (s', f, []) ∧ Enc s' f σ' ∧ MemEnc s' f mem' W ∧
      mem.WritesWithin mem' W.Mem := by
  obtain ⟨F, hF, rfl⟩ := Option.map_eq_some_iff.mp hc
  rw [access_form hF] at hw
  obtain ⟨σ₁, hs, hrip, s₁, he, hE1, hw1⟩ := form_wasm hE hM (formOf_ok hF) _ hw
  rw [form_exec hF, hs] at hx
  simp only [retire, Result.ok.injEq] at hx
  obtain ⟨rfl, rfl⟩ := hx
  obtain ⟨s₂, h2, hE2, hw2⟩ := tail_next hE1 len
  refine ⟨s₂, by rw [exec_append, he]; exact h2, by rw [hrip] at hE2; exact hE2,
    hM.congr (hw2.trans hw1), Silmaril.Process.Memory.WritesWithin.refl _ _⟩

/-- The check passed (flag forms): the code of the first operand runs before the second's. -/
theorem form_holds_flag (hE : Enc s f σ) {mem : Silmaril.Process.Memory} {W : Win}
    (hM : MemEnc s f mem W) {w : Nat} (hw : WOk w) {op : AluOp} {a b : Opd} {wb : Option Reg}
    (next : Word) {rest : List Instr} {r : Store H × Frame × List Val}
    (he : exec s f [] (upCode w (opdCode W w a) ++ (upCode w (opdCode W w b) ++ rest)) = some r) :
    ∀ a' k, (Form.flag ⟨w, op, a, b, wb⟩).access σ next = some (a', k) → W.HoldsK k a' := by
  intro a' k h
  cases ha : a.access w σ next with
  | some _ =>
    have hp : a.access w σ next = some (a', k) := by simpa only [Form.access, ha] using h
    exact opd_holds hE hM hw a next he _ _ hp
  | none =>
    have hb : b.access w σ next = some (a', k) := by simpa only [Form.access, ha] using h
    obtain ⟨x, -, hX⟩ := opd_pure hE hM hw a next (fun _ _ h' => nomatch ha.symm.trans h')
    have he' : exec s f [Val.i64 (up x)] (upCode w (opdCode W w b) ++ rest) = some r := by
      rw [exec_append, hX []] at he; exact he
    exact opd_holds hE hM hw b next he' _ _ hb

/-- **The check passed** (forms). -/
theorem emitForm_holds {W : Win} {i : Silmaril.X86.Ext.Instr} {len : Nat} {code : List Instr}
    (hc : emitForm W i len = some code) (hE : Enc s f σ) {mem : Silmaril.Process.Memory}
    (hM : MemEnc s f mem W) {r : Store H × Frame × List Val} (he : exec s f [] code = some r) :
    ∀ a k, access i σ len = some (a, k) → W.HoldsK k a := by
  obtain ⟨F, hF, rfl⟩ := Option.map_eq_some_iff.mp hc
  rw [access_form hF]
  have hok : F.Ok := formOf_ok hF
  cases F with
  | nop => exact fun _ _ h => nomatch h
  | load L =>
    have e : Form.code W (.load L) ++ nextCode len = upCode L.w (opdCode W L.w L.src) ++
        ([c64 (BitVec.ofNat 64 (64 - L.w)), b64op (.shr (if L.sx then .signed else .unsigned))] ++
        (if L.dsz = .d then [c64 0xffffffff, b64op .and] else []) ++ [gset (.reg L.d)] ++
        nextCode len) := by simp [Form.code]
    exact opd_holds hE hM hok L.src _ (e ▸ he)
  | flag F =>
    obtain ⟨w, op, a, b, wb⟩ := F
    obtain ⟨rest, e⟩ : ∃ rest, Form.code W (.flag ⟨w, op, a, b, wb⟩) ++ nextCode len =
        upCode w (opdCode W w a) ++ (upCode w (opdCode W w b) ++ rest) :=
      ⟨_, by simp only [Form.code, flagPush, msbCode, List.append_assoc]; rfl⟩
    exact form_holds_flag hE hM hok.1 _ (e ▸ he)

/-- **A form's run** (no flag hypothesis): the form's semantics evaluates, and `Ext.exec` retires
it. -/
theorem emitForm_sem {W : Win} {i : Silmaril.X86.Ext.Instr} {len : Nat} {code : List Instr}
    (hc : emitForm W i len = some code) {mem : Silmaril.Process.Memory}
    (hM : MemEnc s f mem W) (hw : ∀ a k, access i σ len = some (a, k) → W.HoldsK k a) :
    ∃ F σ₁, formSem F σ mem (σ.rip + BitVec.ofNat 64 len) = some (σ₁, mem) ∧
      Silmaril.X86.Ext.exec i σ mem len =
        retire (σ.rip + BitVec.ofNat 64 len) (some (σ₁, mem)) := by
  obtain ⟨F, hF, rfl⟩ := Option.map_eq_some_iff.mp hc
  have hok : F.Ok := formOf_ok hF
  rw [form_exec hF]
  set next := σ.rip + BitVec.ofNat 64 len
  have hw' : ∀ a k, F.access σ next = some (a, k) → W.HoldsK k a := fun a k h =>
    hw a k ((access_form hF σ len).trans h)
  have hs : ∃ σ₁, formSem F σ mem next = some (σ₁, mem) := by
    cases F with
    | nop => exact ⟨σ, rfl⟩
    | load L =>
      obtain ⟨x, hx⟩ := opdRead_some hM L.src σ next hw'
      exact ⟨σ.write L.d (loadVal L x), by simp only [formSem, hx, Option.map_some]⟩
    | flag F =>
      obtain ⟨w, op, a, b, wb⟩ := F
      obtain ⟨ha, hb⟩ := flag_acc hok.2.1 hw'
      obtain ⟨x, hx⟩ := opdRead_some hM a σ next ha
      obtain ⟨y, hy⟩ := opdRead_some hM b σ next hb
      exact ⟨flagSem ⟨w, op, a, b, wb⟩ x y σ,
        by simp only [formSem, hx, hy, Option.bind_some, Option.map_some]⟩
  obtain ⟨σ₁, hs⟩ := hs
  exact ⟨F, σ₁, hs, by rw [hs]⟩

/-- **Progress** (forms). -/
theorem emitForm_progress {W : Win} {i : Silmaril.X86.Ext.Instr} {len : Nat} {code : List Instr}
    (hc : emitForm W i len = some code) {mem : Silmaril.Process.Memory}
    (hM : MemEnc s f mem W) (hd : Defined σ.flags)
    (hw : ∀ a k, access i σ len = some (a, k) → W.HoldsK k a) :
    ∃ σ' mem', Silmaril.X86.Ext.exec i σ mem len = .ok σ' mem' ∧ Defined σ'.flags := by
  obtain ⟨F, σ₁, hs, hx⟩ := emitForm_sem hc hM hw
  rw [hx]
  exact ⟨_, _, rfl, (formSem_defined hs hd).1⟩

end Silmaril.Sim.X86.GM
