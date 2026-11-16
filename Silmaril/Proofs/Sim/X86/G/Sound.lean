module

public import Silmaril.Proofs.Sim.X86.G.Store
import Mathlib.Tactic.IntervalCases

/-!
# The G simulator: soundness of each method

For every instruction form `emit` supports and every store encoding an x86 state `σ`
(`Enc s f σ`): if `Silmaril.X86.Ext.exec i σ m len` retires with `σ'`, then the method's code
evaluates (`Silmaril.Wasm.Logic.Core.exec`) to a store encoding `σ'` that differs from `s` only on
the modelled globals, and the memory is unchanged (`emit_sound`).

Structure: `*_core` lemmas for the effect without RIP (`emitCore`), `Enc.next` for `rip += len`,
and three `Enc` shapes (`enc_reg`, `enc_flags`, `enc_flags_reg`) that the instruction proofs
instantiate. The flag values are closed by `flagEnc_msb` (`v >>u 63` encodes `v.msb`) and
`flagEnc_zero`.
-/

@[expose] public section

namespace Silmaril.Sim.X86.G

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (exec exec1 exec_cons exec_append exec_nil)
open Silmaril.X86 (Reg State AluOp Flags)
open Silmaril.X86.Ext (Sz RM Cond Result writeRM readRM retire aluStep)

variable {H : Type} {s : Store H} {f : Frame} {σ : State}

/-! ## Bit-level facts -/

theorem shr63 (v : BitVec 64) : v >>> 63 = b64 v.msb := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.msb_eq_decide]
  have := v.isLt
  by_cases h : 9223372036854775808 ≤ v.toNat <;> simp [b64, h, Nat.shiftRight_eq_div_pow] <;> omega

theorem xor_neg_one (x : BitVec 64) : x ^^^ -1 = ~~~x := by
  rw [show (-1 : BitVec 64) = BitVec.allOnes 64 by decide, BitVec.xor_allOnes]

theorem msb_or_neg (r : BitVec 64) : (r ||| (0 - r)).msb = !(r == 0#64) := by
  rw [BitVec.msb_or, BitVec.msb_eq_decide, BitVec.msb_eq_decide]
  have := r.isLt
  by_cases h : r = 0#64
  · subst h; decide
  · have h' : r.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
    rw [show (r == 0#64) = false by simpa using h, BitVec.toNat_sub,
      show (0 : BitVec 64).toNat = 0 from rfl]
    simp only [Bool.not_false, Bool.or_eq_true, decide_eq_true_eq]
    omega

theorem flagEnc_msb (v : BitVec 64) : FlagEnc (some (Val.i64 (v >>> 63))) (some v.msb) :=
  ⟨v.msb, by rw [shr63], rfl⟩

theorem flagEnc_zero (r : BitVec 64) :
    FlagEnc (some (Val.i64 (1 ^^^ (r ||| (0 - r)) >>> 63))) (some (r == 0#64)) :=
  ⟨r == 0#64, by rw [shr63, msb_or_neg]; cases r == 0#64 <;> rfl, rfl⟩

theorem flagEnc_false : FlagEnc (some (Val.i64 0)) (some false) := ⟨false, rfl, rfl⟩

/-! ## Shapes of encoded stores -/

theorem Layout.upd' (h : Layout s f) {l : Loc} {v : Val} : Layout (Silmaril.Sim.X86.G.upd s f l v) f :=
  h.upd l v

/-- Registers after writing at most one register. -/
def RegsAfter (σ σ' : State) (d : Option (Reg × BitVec 64)) : Prop :=
  ∀ r, σ'.read r = match d with
    | some (d, v) => if r = d then v else σ.read r
    | none => σ.read r

theorem regsAfter_write (σ : State) (d : Reg) (v : BitVec 64) (t : State)
    (ht : t.regs = (σ.write d v).regs) : RegsAfter σ t (some (d, v)) := fun r => by
  show t.regs r = _
  rw [ht]; exact State.read_write σ d r v

theorem regsAfter_same (σ t : State) (ht : t.regs = σ.regs) : RegsAfter σ t none := fun r => by
  show t.regs r = σ.regs r
  rw [ht]

/-- A register write on top of an encoding store, flags unchanged. -/
theorem enc_reg (hE : Enc s f σ) (d : Reg) (v : BitVec 64) (σ' : State)
    (hr : RegsAfter σ σ' (some (d, v))) (hrip : σ'.rip = σ.rip) (hfl : σ'.flags = σ.flags) :
    Enc (upd s f (.reg d) (Val.i64 v)) f σ' := by
  obtain ⟨hl, hrs, hri, hc, hz, hs, ho⟩ := hE
  refine ⟨hl.upd _ _, fun r => ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [gval_upd hl, hrip, hfl, hri, hc, hz, hs, ho, reduceCtorEq, ite_false, Loc.reg.injEq]
  rw [hr r]
  split_ifs <;> simp_all

/-- Four flag writes on top of an encoding store, then (optionally) a register write. -/
theorem enc_flags (hE : Enc s f σ) (c o z g : BitVec 64) (σ' : State)
    (hr : RegsAfter σ σ' none) (hrip : σ'.rip = σ.rip)
    (hc : FlagEnc (some (Val.i64 c)) σ'.flags.carry) (ho : FlagEnc (some (Val.i64 o)) σ'.flags.overflow)
    (hz : FlagEnc (some (Val.i64 z)) σ'.flags.zero) (hg : FlagEnc (some (Val.i64 g)) σ'.flags.sign) :
    Enc (upd (upd (upd (upd s f .cf (Val.i64 c)) f .of (Val.i64 o)) f .zf (Val.i64 z)) f .sf
      (Val.i64 g)) f σ' := by
  obtain ⟨hl, hrs, hri, -, -, -, -⟩ := hE
  refine ⟨hl.upd'.upd'.upd'.upd', fun r => ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [gval_upd hl, gval_upd hl.upd', gval_upd hl.upd'.upd', gval_upd hl.upd'.upd'.upd',
      hrip, hri, reduceCtorEq, ite_false, ite_true, hrs] <;> try assumption
  rw [hr r]

theorem enc_flags_reg (hE : Enc s f σ) (c o z g : BitVec 64) (d : Reg) (v : BitVec 64)
    (σ' : State) (hr : RegsAfter σ σ' (some (d, v))) (hrip : σ'.rip = σ.rip)
    (hc : FlagEnc (some (Val.i64 c)) σ'.flags.carry) (ho : FlagEnc (some (Val.i64 o)) σ'.flags.overflow)
    (hz : FlagEnc (some (Val.i64 z)) σ'.flags.zero) (hg : FlagEnc (some (Val.i64 g)) σ'.flags.sign) :
    Enc (upd (upd (upd (upd (upd s f .cf (Val.i64 c)) f .of (Val.i64 o)) f .zf (Val.i64 z)) f .sf
      (Val.i64 g)) f (.reg d) (Val.i64 v)) f σ' := by
  have h₁ := enc_flags hE c o z g { σ' with regs := σ.regs } (regsAfter_same _ _ rfl) hrip hc ho hz hg
  exact enc_reg h₁ d v σ' (fun r => hr r) rfl rfl

/-- `rip += len` on top of an encoding store. -/
theorem Enc.next (hE : Enc s f σ) (σ' : State) (hr : σ'.regs = σ.regs) (hfl : σ'.flags = σ.flags)
    (w : BitVec 64) (hw : σ'.rip = w) : Enc (upd s f .rip (Val.i64 w)) f σ' := by
  obtain ⟨hl, hrs, hri, hc, hz, hs, ho⟩ := hE
  refine ⟨hl.upd _ _, fun r => ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [gval_upd hl, hw, hfl, hc, hz, hs, ho, reduceCtorEq, ite_false, ite_true]
  · rw [hrs r]; show _ = some (Val.i64 (σ'.regs r)); rw [hr]; rfl

/-! ## The methods, without RIP -/

/-- The common conclusion of a method's soundness: the code evaluates to a store encoding the
x86 result with RIP not yet advanced, and only modelled globals change. -/
def CoreOk (s : Store H) (f : Frame) (code : List Instr) (σ' : State) : Prop :=
  ∃ s₁, exec s f [] code = some (s₁, f, []) ∧ Enc s₁ f σ' ∧ Frames s s₁ f

theorem mov_core (hE : Enc s f σ) (d src : Reg) :
    CoreOk s f [gget (.reg src), gset (.reg d)] (σ.write d (σ.read src)) := by
  have hl := hE.1
  refine ⟨_, ?_, enc_reg hE d (σ.read src) _ (regsAfter_write _ _ _ _ rfl) rfl rfl,
    (Frames.refl s f).upd hl _ _⟩
  simp only [exec_cons, exec1_gget, hE.2.1, Option.map_some, exec1_gset hl, exec_nil]

theorem const_core (hE : Enc s f σ) (d : Reg) (v : BitVec 64) :
    CoreOk s f [c64 v, gset (.reg d)] (σ.write d v) := by
  have hl := hE.1
  refine ⟨_, ?_, enc_reg hE d v _ (regsAfter_write _ _ _ _ rfl) rfl rfl, (Frames.refl s f).upd hl _ _⟩
  simp only [exec_cons, exec1_c64, exec1_gset hl, exec_nil]

/-- The state after `op dst, src` (64-bit registers), RIP not advanced. -/
def aluState (op : AluOp) (d src : Reg) (σ : State) : State :=
  let x := σ.read d
  let y := σ.read src
  if op = .cmp then { σ with flags := Silmaril.X86.Ext.AluOp.flagsN op x y }
  else { σ.write d (Silmaril.X86.Ext.AluOp.resultN op x y) with
    flags := Silmaril.X86.Ext.AluOp.flagsN op x y }

theorem alu_core (hE : Enc s f σ) (op : AluOp) (d src : Reg) :
    CoreOk s f (aluCode op d src) (aluState op d src σ) := by
  have hl := hE.1
  have hr := hE.2.1
  cases op <;>
  · simp (maxDischargeDepth := 20) only [CoreOk, aluCode, carryCode, overflowCode, zeroCode, msbCode,
      notCode, aluWasm, List.cons_append, List.nil_append, exec_cons, exec_nil,
      exec1_gget, hr, hl, Layout.upd, Option.map_some, exec1_c64, exec1_add, exec1_sub, exec1_and,
      exec1_or, exec1_xor, exec1_shr63, exec1_gset, gval_upd, reduceCtorEq, ite_false, ite_true,
      Option.some.injEq, Prod.mk.injEq, and_true, exists_eq_left', xor_neg_one]
    first
    | refine ⟨enc_flags_reg hE _ _ _ _ d _ _ (regsAfter_write _ _ _ _ rfl) rfl
        (flagEnc_msb _) (flagEnc_msb _) (flagEnc_zero _) (flagEnc_msb _), ?_⟩
    | refine ⟨enc_flags_reg hE _ _ _ _ d _ _ (regsAfter_write _ _ _ _ rfl) rfl
        flagEnc_false flagEnc_false (flagEnc_zero _) (flagEnc_msb _), ?_⟩
    | refine ⟨enc_flags hE _ _ _ _ _ (regsAfter_same _ _ rfl) rfl
        (flagEnc_msb _) (flagEnc_msb _) (flagEnc_zero _) (flagEnc_msb _), ?_⟩
    simp (maxDischargeDepth := 20) only [Frames.upd, Frames.refl, hl, Layout.upd]

/-! ## Conditions and `cmov` -/

/-- The concrete flags held by flag bits (PF and AF are irrelevant to the modelled conditions). -/
def cflags (bc bp ba bz bs bo : Bool) : Silmaril.X86.ConcreteFlags := ⟨bc, bp, ba, bz, bs, bo⟩

theorem cond_eval (c : Cond) {code : List Instr} (hc : condCode c = some code) (rs : List Val)
    {bc bz bs bo : Bool} (hcf : gval s f .cf = some (Val.i64 (b64 bc)))
    (hzf : gval s f .zf = some (Val.i64 (b64 bz))) (hsf : gval s f .sf = some (Val.i64 (b64 bs)))
    (hof : gval s f .of = some (Val.i64 (b64 bo))) (bp ba : Bool) :
    exec s f rs code = some (s, f, Val.i64 (b64 (c.holds (cflags bc bp ba bz bs bo))) :: rs) := by
  cases c <;> simp only [condCode, reduceCtorEq, Option.some.injEq] at hc <;> subst hc <;>
    simp only [exec_cons, exec_nil, exec1_gget, hcf, hzf, hsf, hof, Option.map_some, exec1_c64,
      exec1_xor, exec1_or] <;>
    cases bc <;> cases bz <;> cases bs <;> cases bo <;> rfl

theorem cmov_bits (x y : BitVec 64) (t : Bool) :
    x ^^^ ((x ^^^ y) &&& (0 - b64 t)) = if t then y else x := by
  cases t
  · simp [b64]
  · rw [show (0 : BitVec 64) - b64 true = BitVec.allOnes 64 by decide, BitVec.and_allOnes,
      ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    rfl

theorem cmov_core (hE : Enc s f σ) (c : Cond) {code : List Instr} (hc : condCode c = some code)
    (d src : Reg) {taken : Bool} (ht : c.eval σ.flags = some taken) :
    CoreOk s f (cmovCode code d src) (σ.write d (if taken then σ.read src else σ.read d)) := by
  obtain ⟨hl, hr, hri, ⟨bc, hcf, ac⟩, ⟨bz, hzf, az⟩, ⟨bs, hsf, as⟩, ⟨bo, hof, ao⟩⟩ := hE
  have hadm : σ.flags.Admits (cflags bc (σ.flags.parity.getD false) (σ.flags.adjust.getD false)
      bz bs bo) := by
    refine ⟨ac, ?_, ?_, az, as, ao⟩ <;>
    · rcases σ.flags with ⟨_, _ | _, _ | _, _, _, _⟩ <;> simp [Silmaril.X86.FlagValue.Admits, cflags]
  have hv := Cond.eval_sound hadm ht
  have hce := cond_eval (rs := [Val.i64 0, Val.i64 (σ.read d ^^^ σ.read src), Val.i64 (σ.read d)])
    c hc hcf hzf hsf hof (σ.flags.parity.getD false) (σ.flags.adjust.getD false)
  rw [hv] at hce
  refine ⟨_, ?_, enc_reg ⟨hl, hr, hri, ⟨bc, hcf, ac⟩, ⟨bz, hzf, az⟩, ⟨bs, hsf, as⟩, ⟨bo, hof, ao⟩⟩
    d _ _ (regsAfter_write _ _ _ _ rfl) rfl rfl, (Frames.refl s f).upd hl _ _⟩
  rw [cmovCode, exec_append, exec_append]
  simp only [exec_cons, exec_nil, exec1_gget, hr, Option.map_some, exec1_xor, exec1_c64]
  rw [hce]
  simp only [exec1_sub, exec1_and, exec1_xor, exec1_gset hl, cmov_bits]

/-! ## `test`, `dec`, `xor r32, r32` -/

theorem flagEnc_true : FlagEnc (some (Val.i64 1)) (some true) := ⟨true, rfl, rfl⟩

/-- Three flag writes (OF, ZF, SF; CF unchanged) and a register write. -/
theorem enc_ozs_reg (hE : Enc s f σ) (o z g : BitVec 64) (d : Reg) (v : BitVec 64)
    (σ' : State) (hr : RegsAfter σ σ' (some (d, v))) (hrip : σ'.rip = σ.rip)
    (hcf : σ'.flags.carry = σ.flags.carry)
    (ho : FlagEnc (some (Val.i64 o)) σ'.flags.overflow)
    (hz : FlagEnc (some (Val.i64 z)) σ'.flags.zero) (hg : FlagEnc (some (Val.i64 g)) σ'.flags.sign) :
    Enc (upd (upd (upd (upd s f .of (Val.i64 o)) f .zf (Val.i64 z)) f .sf (Val.i64 g)) f
      (.reg d) (Val.i64 v)) f σ' := by
  obtain ⟨hl, hrs, hri, hc, -, -, -⟩ := hE
  refine ⟨hl.upd'.upd'.upd'.upd', fun r => ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [gval_upd hl, gval_upd hl.upd', gval_upd hl.upd'.upd', gval_upd hl.upd'.upd'.upd',
      hrip, hri, hcf, reduceCtorEq, ite_false, ite_true, hrs, Loc.reg.injEq] <;>
    try assumption
  rw [hr r]
  split_ifs <;> simp_all

theorem test_core (hE : Enc s f σ) (d src : Reg) :
    CoreOk s f (testCode d src)
      { σ with flags := Silmaril.X86.Ext.logicFlagsN (σ.read d &&& σ.read src) } := by
  have hl := hE.1
  have hr := hE.2.1
  simp (maxDischargeDepth := 20) only [CoreOk, testCode, zeroCode, msbCode,
    List.cons_append, List.nil_append, exec_cons, exec_nil,
    exec1_gget, hr, hl, Layout.upd, Option.map_some, exec1_c64, exec1_sub, exec1_and,
    exec1_or, exec1_xor, exec1_shr63, exec1_gset, gval_upd, reduceCtorEq, ite_false,
    Option.some.injEq, Prod.mk.injEq, and_true, exists_eq_left']
  refine ⟨enc_flags hE _ _ _ _ _ (regsAfter_same _ _ rfl) rfl flagEnc_false flagEnc_false
    (flagEnc_zero _) (flagEnc_msb _), ?_⟩
  simp (maxDischargeDepth := 20) only [Frames.upd, Frames.refl, hl, Layout.upd]

theorem dec_core (hE : Enc s f σ) (d : Reg) :
    CoreOk s f (decCode d)
      { σ.write d (σ.read d - 1) with
        flags := Silmaril.X86.Ext.decFlagsN (σ.read d) σ.flags } := by
  have hl := hE.1
  have hr := hE.2.1
  simp (maxDischargeDepth := 20) only [CoreOk, decCode, overflowCode, zeroCode, msbCode,
    List.cons_append, List.nil_append, exec_cons, exec_nil,
    exec1_gget, hr, hl, Layout.upd, Option.map_some, exec1_c64, exec1_sub, exec1_and,
    exec1_or, exec1_xor, exec1_shr63, exec1_gset, gval_upd, reduceCtorEq, ite_false,
    Option.some.injEq, Prod.mk.injEq, and_true, exists_eq_left']
  refine ⟨enc_ozs_reg hE _ _ _ d _ _ (regsAfter_write _ _ _ _ rfl) rfl rfl
    (flagEnc_msb _) (flagEnc_zero _) (flagEnc_msb _), ?_⟩
  simp (maxDischargeDepth := 20) only [Frames.upd, Frames.refl, hl, Layout.upd]

theorem zero32_core (hE : Enc s f σ) (d : Reg) (p : Option Bool) :
    CoreOk s f (zero32Code d)
      { σ.write d 0 with flags := ⟨some false, p, none, some true, some false, some false⟩ } := by
  have hl := hE.1
  simp (maxDischargeDepth := 20) only [CoreOk, zero32Code, exec_cons, exec_nil, hl, Layout.upd,
    exec1_c64, exec1_gset, Option.some.injEq, Prod.mk.injEq, and_true, exists_eq_left']
  refine ⟨enc_flags_reg hE _ _ _ _ d _ _ (regsAfter_write _ _ _ _ rfl) rfl
    flagEnc_false flagEnc_false flagEnc_true flagEnc_false, ?_⟩
  simp (maxDischargeDepth := 20) only [Frames.upd, Frames.refl, hl, Layout.upd]

/-! ## 32-bit `mov` and `bswap` -/

theorem exec1_shl (rs : List Val) (x k : BitVec 64) :
    exec1 s f (Val.i64 k :: Val.i64 x :: rs) (b64op .shl) =
      some (s, f, Val.i64 (x <<< (k.toNat % 64)) :: rs) := by
  rw [exec1_b64op]; rfl

theorem exec1_shru (rs : List Val) (x k : BitVec 64) :
    exec1 s f (Val.i64 k :: Val.i64 x :: rs) (b64op (.shr .unsigned)) =
      some (s, f, Val.i64 (x >>> (k.toNat % 64)) :: rs) := by
  rw [exec1_b64op]; rfl

/-- The value `bswap32Code` computes from the register's value. -/
def bswap32Val (x : BitVec 64) : BitVec 64 :=
  (x &&& 0xff) <<< 24 ||| (x >>> 8 &&& 0xff) <<< 16 ||| (x >>> 16 &&& 0xff) <<< 8 |||
    (x >>> 24 &&& 0xff)

theorem mov32_core (hE : Enc s f σ) (d src : Reg) :
    CoreOk s f (mov32Code d src) (σ.write d (σ.read src &&& 0xffffffff)) := by
  have hl := hE.1
  refine ⟨_, ?_, enc_reg hE d _ _ (regsAfter_write _ _ _ _ rfl) rfl rfl,
    (Frames.refl s f).upd hl _ _⟩
  simp only [mov32Code, exec_cons, exec1_gget, hE.2.1, Option.map_some, exec1_c64, exec1_and,
    exec1_gset hl, exec_nil]

theorem bswap32_core (hE : Enc s f σ) (d : Reg) :
    CoreOk s f (bswap32Code d) (σ.write d (bswap32Val (σ.read d))) := by
  have hl := hE.1
  refine ⟨_, ?_, enc_reg hE d _ _ (regsAfter_write _ _ _ _ rfl) rfl rfl,
    (Frames.refl s f).upd hl _ _⟩
  simp only [bswap32Code, exec_cons, exec1_gget, hE.2.1, Option.map_some, exec1_c64, exec1_and,
    exec1_or, exec1_shl, exec1_shru, exec1_gset hl, exec_nil, bswap32Val]
  rfl

theorem mov32_val (x : BitVec 64) : (x.setWidth 32).setWidth 64 = x &&& 0xffffffff := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (0xffffffff : BitVec 64).toNat = 2 ^ 32 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  simp only [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have := x.isLt; omega)

/-- Silmaril's `byteSwap32` of the low half, zero-extended, is `bswap32Val` (bit by bit). -/
theorem bswap32_val (x : BitVec 64) :
    (Silmaril.X86.Ext.byteSwap32 (x.setWidth 32)).setWidth 64 = bswap32Val x := by
  simp only [Silmaril.X86.Ext.byteSwap32, bswap32Val]
  ext i hi
  simp only [BitVec.getElem_setWidth, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_setWidth, BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.getElem_and,
    BitVec.getElem_ushiftRight]
  interval_cases i <;> simp

/-! ## 32-bit ALU, `test`, `mov imm32`

The 32-bit operands are embedded in the high half of a 64-bit word (`e32`); sums, differences
and bitwise operations commute with the embedding, and the most significant bit is preserved,
so the 64-bit flag formulas compute the 32-bit flags. -/

/-- The high-half embedding. -/
def e32 (x : BitVec 32) : BitVec 64 := x.setWidth 64 <<< 32


theorem shl32 (v : BitVec 64) : v <<< 32 = e32 (v.setWidth 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [e32, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth]
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  omega


theorem e32_add (x y : BitVec 32) : e32 x + e32 y = e32 (x + y) := by
  apply BitVec.eq_of_toNat_eq
  simp [e32, BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_setWidth]
  omega

theorem e32_sub (x y : BitVec 32) : e32 x - e32 y = e32 (x - y) := by
  apply BitVec.eq_of_toNat_eq
  simp [e32, BitVec.toNat_shiftLeft, BitVec.toNat_sub, BitVec.toNat_setWidth]
  omega

theorem e32_msb (z : BitVec 32) : (e32 z).msb = z.msb := by
  simp [e32, BitVec.msb_eq_getLsbD_last]

theorem e32_and (x y : BitVec 32) : e32 x &&& e32 y = e32 (x &&& y) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  by_cases h : i < 32 <;> simp [e32, h, hi]
theorem e32_or (x y : BitVec 32) : e32 x ||| e32 y = e32 (x ||| y) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  by_cases h : i < 32 <;> simp [e32, h, hi]
theorem e32_xor (x y : BitVec 32) : e32 x ^^^ e32 y = e32 (x ^^^ y) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  by_cases h : i < 32 <;> simp [e32, h, hi]
theorem e32_zero (z : BitVec 32) : (e32 z == 0#64) = (z == 0#32) := by
  have h : e32 z = 0#64 ↔ z = 0#32 := by
    constructor
    · intro h; apply BitVec.eq_of_toNat_eq
      have := congrArg BitVec.toNat h
      simp [e32, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq] at this ⊢; omega
    · rintro rfl; rfl
  by_cases hz : z = 0#32
  · subst hz; rfl
  · simp [hz, h]
theorem e32_shr (z : BitVec 32) : e32 z >>> 32 = z.setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  simp [e32, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega

def alu32State (op : AluOp) (d src : Reg) (σ : State) : State :=
  let x := (σ.read d).setWidth 32
  let y := (σ.read src).setWidth 32
  if op = .cmp then { σ with flags := Silmaril.X86.Ext.AluOp.flagsN op x y }
  else { σ.write d ((Silmaril.X86.Ext.AluOp.resultN op x y).setWidth 64) with
    flags := Silmaril.X86.Ext.AluOp.flagsN op x y }

theorem k32 : (BitVec.toNat (32 : BitVec 64)) % 64 = 32 := rfl
theorem k63 : (BitVec.toNat (63 : BitVec 64)) % 64 = 63 := rfl
theorem fe_msb {v : BitVec 64} {b : Bool} (h : v.msb = b) : FlagEnc (some (Val.i64 (v >>> 63))) (some b) :=
  h ▸ flagEnc_msb v
theorem fe_zero (z : BitVec 32) :
    FlagEnc (some (Val.i64 (1 ^^^ (e32 z ||| 0 - e32 z) >>> 63))) (some (z == 0#32)) := by
  rw [← e32_zero]; exact flagEnc_zero _

theorem alu32State_flags (op : AluOp) (d src : Reg) (σ : State) :
    (alu32State op d src σ).flags =
      Silmaril.X86.Ext.AluOp.flagsN op ((σ.read d).setWidth 32) ((σ.read src).setWidth 32) := by
  unfold alu32State; split <;> rfl

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 4000 in
/-- `op r32, r32`. -/
theorem alu32_core (hE : Enc s f σ) (op : AluOp) (d src : Reg) :
    CoreOk s f (alu32Code op d src) (alu32State op d src σ) := by
  cases op <;>
  · simp (maxDischargeDepth := 20) only [CoreOk, alu32Code, carryCode, overflowCode, zeroCode, msbCode,
      notCode, aluWasm, List.cons_append, List.nil_append, exec_cons, exec_nil,
      exec1_gget, hE.2.1, hE.1, Layout.upd, Option.map_some, exec1_c64, exec1_add, exec1_sub, exec1_and,
      exec1_or, exec1_xor, exec1_shr63, exec1_shl, exec1_shru, exec1_gset, gval_upd, reduceCtorEq, ite_false, ite_true,
      Option.some.injEq, Prod.mk.injEq, and_true, exists_eq_left', xor_neg_one, k32, k63]
    simp only [shl32, e32_add, e32_sub, e32_and, e32_or, e32_xor, e32_shr]
    first
    | refine ⟨enc_flags_reg hE _ _ _ _ d _ _ (regsAfter_write _ _ _ _ rfl) rfl ?_ ?_ ?_ ?_, ?_⟩
    | refine ⟨enc_flags hE _ _ _ _ _ (regsAfter_same _ _ rfl) rfl ?_ ?_ ?_ ?_, ?_⟩
    all_goals first
      | simp (maxDischargeDepth := 20) only [Frames.upd, Frames.refl, hE.1, Layout.upd]
      | exact flagEnc_false
      | exact fe_zero _
      | (rw [alu32State_flags]; apply fe_msb
         simp [Silmaril.X86.Ext.AluOp.flagsN, Silmaril.X86.Ext.addFlagsN,
          Silmaril.X86.Ext.subFlagsN, Silmaril.X86.Ext.logicFlagsN, Silmaril.X86.Ext.addCarryN,
          Silmaril.X86.Ext.addOverflowN, Silmaril.X86.Ext.subBorrowN, Silmaril.X86.Ext.subOverflowN,
          BitVec.msb_and, BitVec.msb_or, BitVec.msb_xor, BitVec.msb_not, e32_msb])

set_option linter.unusedSimpArgs false in
theorem test32_core (hE : Enc s f σ) (d src : Reg) :
    CoreOk s f (test32Code d src)
      { σ with flags := Silmaril.X86.Ext.logicFlagsN ((σ.read d).setWidth 32 &&& (σ.read src).setWidth 32) } := by
  have hl := hE.1
  have hr := hE.2.1
  simp (maxDischargeDepth := 20) only [CoreOk, test32Code, zeroCode, msbCode,
    List.cons_append, List.nil_append, exec_cons, exec_nil,
    exec1_gget, hr, hl, Layout.upd, Option.map_some, exec1_c64, exec1_sub, exec1_and,
    exec1_or, exec1_xor, exec1_shl, exec1_shru, exec1_gset, gval_upd, reduceCtorEq, ite_false,
    Option.some.injEq, Prod.mk.injEq, and_true, exists_eq_left', k32, k63]
  simp only [shl32, e32_and]
  refine ⟨enc_flags hE _ _ _ _ _ (regsAfter_same _ _ rfl) rfl flagEnc_false flagEnc_false
    (fe_zero _) (fe_msb ?_), ?_⟩
  · simp [Silmaril.X86.Ext.logicFlagsN, e32_msb]
  · simp (maxDischargeDepth := 20) only [Frames.upd, Frames.refl, hl, Layout.upd]

/-! ## RIP and whole methods -/

theorem next_ok {code : List Instr} {t : State} (h : CoreOk s f code t) (len : Nat) :
    ∃ s', exec s f [] (code ++ nextCode len) = some (s', f, []) ∧
      Enc s' f { t with rip := t.rip + BitVec.ofNat 64 len } ∧ Frames s s' f := by
  obtain ⟨s₁, he, hE, hF⟩ := h
  refine ⟨_, ?_, hE.next { t with rip := t.rip + BitVec.ofNat 64 len } rfl rfl _ rfl,
    hF.upd hE.1 _ _⟩
  rw [exec_append, he]
  simp only [nextCode, exec_cons, exec_nil, exec1_gget, hE.2.2.1, Option.map_some, exec1_c64,
    exec1_add, exec1_gset hE.1]

/-! ## Soundness of `emit` -/

theorem xor32_cases {d s : Reg} {code : List Instr}
    (h : (if d = s then some (zero32Code d) else some (alu32Code .xor d s)) = some code) :
    (d = s ∧ code = zero32Code d) ∨ code = alu32Code .xor d s := by
  split at h
  · exact .inl ⟨‹_›, (Option.some.inj h).symm⟩
  · exact .inr (Option.some.inj h).symm

/-- The instructions `emitCore` supports, and their code. -/
theorem emitCore_cases {i : Silmaril.X86.Ext.Instr} {code : List Instr} (h : emitCore i = some code) :
    (∃ d src, i = .mov .q (.reg d) src ∧ code = [gget (.reg src), gset (.reg d)]) ∨
    (∃ d imm, i = .movI .q (.reg d) imm ∧ code = [c64 (imm.signExtend 64), gset (.reg d)]) ∨
    (∃ d imm, i = .movabs d imm ∧ code = [c64 imm, gset (.reg d)]) ∨
    (∃ op d src, i = .alu .q op (.reg d) src ∧ code = aluCode op d src) ∨
    (∃ c cc d src, i = .cmov .q c d (.reg src) ∧ condCode c = some cc ∧ code = cmovCode cc d src) ∨
    (∃ d src, i = .test .q (.reg d) src ∧ code = testCode d src) ∨
    (∃ d, i = .incdec .q true (.reg d) ∧ code = decCode d) ∨
    (∃ d, i = .alu .d .xor (.reg d) d ∧ code = zero32Code d) ∨
    (∃ d src, i = .mov .d (.reg d) src ∧ code = mov32Code d src) ∨
    (∃ d, i = .bswap .d d ∧ code = bswap32Code d) ∨
    (∃ op d src, i = .alu .d op (.reg d) src ∧ code = alu32Code op d src) ∨
    (∃ d src, i = .test .d (.reg d) src ∧ code = test32Code d src) ∨
    (∃ d imm, i = .movI32 d imm ∧ code = movI32Code d imm) := by
  revert h
  unfold emitCore
  split
  · intro h; exact .inl ⟨_, _, rfl, (Option.some.inj h).symm⟩
  · intro h; exact .inr (.inl ⟨_, _, rfl, (Option.some.inj h).symm⟩)
  · intro h; exact .inr (.inr (.inl ⟨_, _, rfl, (Option.some.inj h).symm⟩))
  · intro h; exact .inr (.inr (.inr (.inl ⟨_, _, _, rfl, (Option.some.inj h).symm⟩)))
  · next c d s =>
    intro h
    obtain ⟨cc, hc, hcode⟩ : ∃ cc, condCode c = some cc ∧ cmovCode cc d s = code :=
      Option.map_eq_some_iff.mp h
    exact .inr (.inr (.inr (.inr (.inl ⟨_, _, _, _, rfl, hc, hcode.symm⟩))))
  · intro h; exact .inr (.inr (.inr (.inr (.inr (.inl ⟨_, _, rfl, (Option.some.inj h).symm⟩)))))
  · intro h
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨_, rfl, (Option.some.inj h).symm⟩))))))
  · next d s =>
    intro h
    rcases xor32_cases h with ⟨hds, hc⟩ | hc
    · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨_, by rw [hds], hc⟩)))))))
    · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
        ⟨.xor, _, _, rfl, hc⟩))))))))))
  · intro h
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨_, _, rfl, (Option.some.inj h).symm⟩))))))))
  · intro h
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨_, rfl, (Option.some.inj h).symm⟩)))))))))
  · intro h
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨_, _, _, rfl, (Option.some.inj h).symm⟩))))))))))
  · intro h
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨_, _, rfl, (Option.some.inj h).symm⟩)))))))))))
  · intro h
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (⟨_, _, rfl, (Option.some.inj h).symm⟩))))))))))))
  · intro h; cases h

theorem zero32_state (σ : State) (d : Reg) :
    Silmaril.X86.Ext.Sz.d.write σ d ((σ.read d).setWidth 32 ^^^ (σ.read d).setWidth 32) =
      σ.write d 0 := by
  simp [Silmaril.X86.Ext.Sz.write]

/-- **Shape of a supported instruction's result**: from `Ext.exec`, the memory is unchanged,
RIP advances by the length, the instruction is not `ret`, defined modelled flags stay
defined, and the result is the method's state `t` (RIP not advanced) with RIP advanced. -/
theorem core_shape {i : Silmaril.X86.Ext.Instr} {core : List Instr} (hc : emitCore i = some core)
    {σ σ' : State} {m m' : Silmaril.Process.Memory} {len : Nat}
    (hx : Silmaril.X86.Ext.exec i σ m len = .ok σ' m') :
    m' = m ∧ σ'.rip = σ.rip + BitVec.ofNat 64 len ∧ i ≠ .ret ∧
      (Defined σ.flags → Defined σ'.flags) ∧
      ∀ s : Store H, Enc s f σ → CoreOk s f core { σ' with rip := σ.rip } := by
  rcases emitCore_cases hc with
    ⟨d, src, rfl, rfl⟩ | ⟨d, imm, rfl, rfl⟩ | ⟨d, imm, rfl, rfl⟩ | ⟨op, d, src, rfl, rfl⟩ |
    ⟨c, cc, d, src, rfl, hcc, rfl⟩ | ⟨d, src, rfl, rfl⟩ | ⟨d, rfl, rfl⟩ | ⟨d, rfl, rfl⟩ |
    ⟨d, src, rfl, rfl⟩ | ⟨d, rfl, rfl⟩ | ⟨op, d, src, rfl, rfl⟩ | ⟨d, src, rfl, rfl⟩ |
    ⟨d, imm, rfl, rfl⟩
  · simp only [Silmaril.X86.Ext.exec, writeRM, Sz.read_q, Sz.write_q, retire,
      Result.ok.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    exact ⟨rfl, rfl, nofun, id, fun s hE => mov_core hE d src⟩
  · simp only [Silmaril.X86.Ext.exec, writeRM, retire, Result.ok.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    exact ⟨rfl, rfl, nofun, id, fun s hE => const_core hE d _⟩
  · simp only [Silmaril.X86.Ext.exec, retire, Result.ok.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    exact ⟨rfl, rfl, nofun, id, fun s hE => const_core hE d _⟩
  · cases op <;>
      simp only [Silmaril.X86.Ext.exec, aluStep, readRM, writeRM, Sz.read_q, retire,
        reduceCtorEq, ite_false, ite_true, Option.map_some, Result.ok.injEq] at hx <;>
      obtain ⟨rfl, rfl⟩ := hx <;>
      exact ⟨rfl, rfl, nofun, fun _ => ⟨rfl, rfl, rfl, rfl⟩, fun s hE => alu_core hE _ d src⟩
  · simp only [Silmaril.X86.Ext.exec, readRM, Sz.read_q] at hx
    cases ht : c.eval σ.flags with
    | none => simp [ht] at hx
    | some taken =>
      simp only [ht, retire, Result.ok.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact ⟨rfl, rfl, nofun, id, fun s hE => cmov_core hE c hcc d src ht⟩
  · simp only [Silmaril.X86.Ext.exec, readRM, Sz.read_q, retire] at hx
    obtain ⟨rfl, rfl⟩ := hx
    exact ⟨rfl, rfl, nofun, fun _ => ⟨rfl, rfl, rfl, rfl⟩, fun s hE => test_core hE d src⟩
  · simp only [Silmaril.X86.Ext.exec, readRM, writeRM, Sz.read_q, ite_true,
      Option.map_some, retire, Result.ok.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    exact ⟨rfl, rfl, nofun, fun h => ⟨h.1, rfl, rfl, rfl⟩, fun s hE => dec_core hE d⟩
  · simp only [Silmaril.X86.Ext.exec, aluStep, readRM, writeRM, retire, reduceCtorEq,
      ite_false, Option.map_some, Result.ok.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    refine ⟨rfl, rfl, nofun, fun _ => ⟨rfl, rfl, rfl, rfl⟩, fun s hE => ?_⟩
    have h := zero32_core hE d (some (Silmaril.X86.Ext.parityN (0 : BitVec 32)))
    convert h using 1
    simp only [Silmaril.X86.Ext.AluOp.resultN, Silmaril.X86.Ext.AluOp.flagsN,
      Silmaril.X86.Ext.logicFlagsN, Sz.read, Sz.write, BitVec.xor_self,
      Silmaril.X86.Ext.isZeroN, BitVec.setWidth_zero]
    rfl
  · simp only [Silmaril.X86.Ext.exec, writeRM, retire, Result.ok.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    refine ⟨rfl, rfl, nofun, id, fun s hE => ?_⟩
    have h := mov32_core hE d src
    simp only [Sz.write, Sz.read, Sz.bits, mov32_val]
    exact h
  · simp only [Silmaril.X86.Ext.exec, retire, Result.ok.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    refine ⟨rfl, rfl, nofun, id, fun s hE => ?_⟩
    have h := bswap32_core hE d
    simp only [Sz.write, Sz.read, Sz.bits, Silmaril.X86.Ext.byteSwap, bswap32_val]
    exact h
  · cases op <;>
      simp only [Silmaril.X86.Ext.exec, aluStep, readRM, writeRM, retire, reduceCtorEq,
        ite_false, ite_true, Option.map_some, Result.ok.injEq] at hx <;>
      obtain ⟨rfl, rfl⟩ := hx <;>
      exact ⟨rfl, rfl, nofun, fun _ => ⟨rfl, rfl, rfl, rfl⟩, fun s hE => alu32_core hE _ d src⟩
  · simp only [Silmaril.X86.Ext.exec, readRM, retire, Option.map_some, Result.ok.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    exact ⟨rfl, rfl, nofun, fun _ => ⟨rfl, rfl, rfl, rfl⟩, fun s hE => test32_core hE d src⟩
  · simp only [Silmaril.X86.Ext.exec, retire, Result.ok.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    exact ⟨rfl, rfl, nofun, id, fun s hE => const_core hE d _⟩

/-- **Soundness of each method.** If the store encodes `σ` and the instruction retires on
`Silmaril.X86.Ext.exec` (with byte length `len`) with `σ'` and memory `m'`, then the method's code
evaluates to a store encoding `σ'`, changing only modelled globals, and the memory is
unchanged. -/
theorem emit_sound {i : Silmaril.X86.Ext.Instr} {len : Nat} {code : List Instr}
    (hc : emit i len = some code) {σ σ' : State} (hE : Enc s f σ) {m m' : Silmaril.Process.Memory}
    (hx : Silmaril.X86.Ext.exec i σ m len = .ok σ' m') :
    m' = m ∧ ∃ s', exec s f [] code = some (s', f, []) ∧ Enc s' f σ' ∧ Frames s s' f := by
  obtain ⟨core, hcore, rfl⟩ := Option.map_eq_some_iff.mp hc
  obtain ⟨hm, hrip, -, -, hok⟩ := core_shape hcore hx
  refine ⟨hm, ?_⟩
  have := next_ok (hok s hE) len
  have he : { { σ' with rip := σ.rip } with rip := σ.rip + BitVec.ofNat 64 len } = σ' := by
    rw [← hrip]
  rwa [he] at this

/-- Every instruction with a method falls through: RIP advances by its length, it is not
`ret`, and the memory is unchanged. -/
theorem emit_rip {i : Silmaril.X86.Ext.Instr} {len : Nat} {code : List Instr}
    (hc : emit i len = some code) {σ σ' : State} {m m' : Silmaril.Process.Memory}
    (hx : Silmaril.X86.Ext.exec i σ m len = .ok σ' m') :
    σ'.rip = σ.rip + BitVec.ofNat 64 len ∧ i ≠ .ret ∧ m' = m := by
  obtain ⟨core, hcore, rfl⟩ := Option.map_eq_some_iff.mp hc
  obtain ⟨hm, hrip, hr, -⟩ := core_shape (f := ({} : Frame)) (H := Nat) hcore hx
  exact ⟨hrip, hr, hm⟩

end Silmaril.Sim.X86.G
