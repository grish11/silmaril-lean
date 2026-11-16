module

public import Silmaril.Sim.X86.Loop.Thms
public import Silmaril.Sim.X86.G.Thms
public import Silmaril.Sim.Reduce.Loop.Thms
public import Silmaril.X86.BlockCert9.Thms

/-!
# `sat_add_u32` (pinned leaf-arith ELF, `0x401400`): the Wasm problem

```
 0: 31 d2          xor  edx, edx           10: b8 ff ff ff ff  mov eax, -1
 2: 01 f7          add  edi, esi           15: c3              ret
 4: 72 10          jb   16                 16: ba 01 00 00 00  mov edx, 1
 6: 89 f8          mov  eax, edi           1b: eb e9           jmp 6
 8: 85 d2          test edx, edx
 a: 75 04          jne  10
 c: c3             ret
```

`satRel`: the body at relative offsets (no `ret`s: a run of the dispatcher ends at `+0xc` or
`+0x15`). The Wasm-side facts, all about the G dispatcher code (`Silmaril.Sim.X86.Loop`) (`dispCode`) over Wasm
globals only:

* `step*`: each entry's generated code evaluated by `simp` (`sat_step`);
* `measured_step`: under the cut-point invariant `PCM` (one assertion per entry, with a measure)
  every entry evaluates and decreases the measure — this one fact is both the dispatcher's
  partial-correctness obligation (`wasm_solution`, `dispatch_hwp`) and its ranking
  (`ranked`, `Silmaril.Sim.Reduce.Loop.Ranked`, for termination);
* **`wasm_solution`**: `LProblem` of the dispatcher: the run ends at a `ret` with
  `rax = zext (sat_add (low32 rdi) (low32 rsi))`, every register but `rax rdx rdi` unchanged.
-/

@[expose] public section

namespace Silmaril.Sim.ElfVerify.SatAdd

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.X86 (Reg Word)
open Silmaril.Sim.X86.G Silmaril.Sim.X86.Loop
open Silmaril.Wasm.Logic.Core (exec exec_cons exec_nil)

/-- The body at relative offsets. -/
def satRel : Silmaril.Sim.Reduce.Loop.RTab :=
  [(0, .alu .d .xor (.reg .rdx) .rdx, 2), (2, .alu .d .add (.reg .rdi) .rsi, 2),
   (4, .jcc8 .b 0x10, 2), (6, .mov .d (.reg .rax) .rdi, 2), (8, .test .d (.reg .rdx) .rdx, 2),
   (0xa, .jcc8 .ne 4, 2), (0x10, .movI32 .rax 0xffffffff, 5), (0x16, .movI32 .rdx 1, 5),
   (0x1b, .jmp8 0xe9, 2)]

/-- The body placed at `b`. -/
def satTab (b : Word) : XTab := Silmaril.Sim.Reduce.Loop.place b satRel

/-- The C function (`arith.c`): `s = a + b; return s < a ? 0xffffffff : s`. -/
def satAdd (a b : BitVec 32) : BitVec 32 := if (a + b).ult a then 0xffffffff#32 else a + b

variable {H : Type} {s : Store H} {f : Frame}

/-- The globals the code touches, with the layout; every other register is `R`'s. -/
def Vals (s : Store H) (f : Frame) (R : Reg → Word) (rip rax rdx rdi cf zf : Word) : Prop :=
  Layout s f ∧ gval s f .rip = some (Val.i64 rip) ∧ gval s f (.reg .rax) = some (Val.i64 rax) ∧
    gval s f (.reg .rdx) = some (Val.i64 rdx) ∧ gval s f (.reg .rdi) = some (Val.i64 rdi) ∧
    gval s f .cf = some (Val.i64 cf) ∧ gval s f .zf = some (Val.i64 zf) ∧
    ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rdi → gval s f (.reg r) = some (Val.i64 (R r))

/-- Evaluate one entry's code on a store given by `Vals`. -/
syntax "sat_step" : tactic
macro_rules
  | `(tactic| sat_step) => `(tactic| (
    simp (maxDischargeDepth := 20) (contextual := true) only [aluCode, carryCode, overflowCode,
      zeroCode, msbCode, notCode, aluWasm, nextCode, testCode, zero32Code, jccCode, jmpCode,
      alu32Code, test32Code, movI32Code, mov32Code,
      List.cons_append, List.nil_append, exec_cons, exec_nil,
      exec1_gget, Layout.upd, Option.map_some, exec1_c64, exec1_add, exec1_sub,
      exec1_and, exec1_or, exec1_xor, exec1_shl, exec1_shru, k32, k63, exec1_gset, gval_upd,
      reduceCtorEq, ite_false, ite_true, Option.some.injEq, Prod.mk.injEq, and_true,
      exists_eq_left', Vals, true_and, Loc.reg.injEq, val_i64_inj, BitVec.and_self, exists_eq',
      ne_eq, not_false_eq_true, implies_true, *] <;>
    first | rfl | (refine ⟨?_, ?_⟩ <;> rfl) | exact ⟨_, rfl, rfl⟩ | exact ⟨_, rfl⟩ | skip))

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

theorem step0 {R : Reg → Word} {rip rax rdx rdi cf zf : Word}
    (h : Vals s f R rip rax rdx rdi cf zf) :
    ∃ s', exec s f [] (zero32Code .rdx ++ nextCode 2) = some (s', f, []) ∧
      Vals s' f R (rip + 2) rax 0 rdi 0 1 := by
  obtain ⟨hl, h1, h2, h3, h4, h5, h6, h7⟩ := h
  sat_step

/-- The carry of `add r32, r32` as the Wasm code computes it. -/
theorem carry32 (x y : BitVec 32) :
    (e32 (x &&& y) ||| e32 (x ||| y) &&& ~~~e32 (x + y)) >>> 63 = b64 ((x + y).ult x) := by
  have h : Silmaril.X86.Ext.addCarryN x y = (x + y).ult x :=
    Silmaril.X86.BlockCert9.addCarryN_eq_ult x y
  rw [shr63, ← h]
  simp only [Silmaril.X86.Ext.addCarryN, BitVec.msb_and, BitVec.msb_or, BitVec.msb_not, e32_msb]
  rfl

set_option maxRecDepth 4000 in
theorem step2 {R : Reg → Word} {rip rax rdx rdi cf zf : Word}
    (h : Vals s f R rip rax rdx rdi cf zf) :
    ∃ s', exec s f [] (alu32Code .add .rdi .rsi ++ nextCode 2) = some (s', f, []) ∧
      ∃ zf', Vals s' f R (rip + 2) rax rdx
        ((rdi.setWidth 32 + (R .rsi).setWidth 32).setWidth 64)
        (b64 ((rdi.setWidth 32 + (R .rsi).setWidth 32).ult (rdi.setWidth 32))) zf' := by
  obtain ⟨hl, h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hsi := h7 .rsi (by decide) (by decide) (by decide)
  sat_step
  refine ⟨_, rfl, ?_, ?_, rfl⟩
  · rw [shl32, shl32, e32_add, e32_shr]
  · rw [shl32, shl32, e32_add, e32_and, e32_or, xor_neg_one, carry32]

theorem step4 {R : Reg → Word} {rip rax rdx rdi cf zf : Word}
    (h : Vals s f R rip rax rdx rdi cf zf) :
    ∃ s', exec s f [] (jccCode [gget .cf] 0x10 2) = some (s', f, []) ∧
      Vals s' f R (rip + 2 + ((0 - cf) &&& 0x10)) rax rdx rdi cf zf := by
  obtain ⟨hl, h1, h2, h3, h4, h5, h6, h7⟩ := h
  sat_step

theorem step6 {R : Reg → Word} {rip rax rdx rdi cf zf : Word}
    (h : Vals s f R rip rax rdx rdi cf zf) :
    ∃ s', exec s f [] (mov32Code .rax .rdi ++ nextCode 2) = some (s', f, []) ∧
      Vals s' f R (rip + 2) (rdi &&& 0xffffffff) rdx rdi cf zf := by
  obtain ⟨hl, h1, h2, h3, h4, h5, h6, h7⟩ := h
  sat_step

set_option maxRecDepth 4000 in
theorem step8 {R : Reg → Word} {rip rax rdx rdi cf zf : Word}
    (h : Vals s f R rip rax rdx rdi cf zf) :
    ∃ s', exec s f [] (test32Code .rdx .rdx ++ nextCode 2) = some (s', f, []) ∧
      Vals s' f R (rip + 2) rax rdx rdi 0 (b64 (rdx.setWidth 32 == 0#32)) := by
  obtain ⟨hl, h1, h2, h3, h4, h5, h6, h7⟩ := h
  sat_step
  refine ⟨rfl, ?_⟩
  rw [shr63, msb_or_neg, shl32, e32_zero]
  cases (BitVec.setWidth 32 rdx == 0#32) <;> rfl

theorem stepA {R : Reg → Word} {rip rax rdx rdi cf zf : Word}
    (h : Vals s f R rip rax rdx rdi cf zf) :
    ∃ s', exec s f [] (jccCode [gget .zf, c64 1, b64op .xor] 4 2) = some (s', f, []) ∧
      Vals s' f R (rip + 2 + ((0 - (zf ^^^ 1)) &&& 4)) rax rdx rdi cf zf := by
  obtain ⟨hl, h1, h2, h3, h4, h5, h6, h7⟩ := h
  sat_step

theorem step10 {R : Reg → Word} {rip rax rdx rdi cf zf : Word}
    (h : Vals s f R rip rax rdx rdi cf zf) :
    ∃ s', exec s f [] (movI32Code .rax 0xffffffff ++ nextCode 5) = some (s', f, []) ∧
      Vals s' f R (rip + 5) 0xffffffff rdx rdi cf zf := by
  obtain ⟨hl, h1, h2, h3, h4, h5, h6, h7⟩ := h
  sat_step

theorem step16 {R : Reg → Word} {rip rax rdx rdi cf zf : Word}
    (h : Vals s f R rip rax rdx rdi cf zf) :
    ∃ s', exec s f [] (movI32Code .rdx 1 ++ nextCode 5) = some (s', f, []) ∧
      Vals s' f R (rip + 5) rax 1 rdi cf zf := by
  obtain ⟨hl, h1, h2, h3, h4, h5, h6, h7⟩ := h
  sat_step

theorem step1b {R : Reg → Word} {rip rax rdx rdi cf zf : Word}
    (h : Vals s f R rip rax rdx rdi cf zf) :
    ∃ s', exec s f [] (jmpCode 0xe9 2) = some (s', f, []) ∧
      Vals s' f R (rip + (BitVec.ofNat 64 2 + (0xe9 : BitVec 8).signExtend 64)) rax rdx rdi cf zf := by
  obtain ⟨hl, h1, h2, h3, h4, h5, h6, h7⟩ := h
  sat_step

/-! ## The cut points, with a measure -/

/-- The specification: the run ends at one of the two `ret`s with `rax = zext (sat_add a b)`
for `a b` the low halves of `rdi rsi`, every register but `rax rdx rdi` unchanged. -/
def SatPost (R : Reg → Word) (b : Word) (R' : Reg → Word) (w' : Word) : Prop :=
  R' .rax = (satAdd ((R .rdi).setWidth 32) ((R .rsi).setWidth 32)).setWidth 64 ∧
    (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rdi → R' r = R r) ∧
    (w' = b + BitVec.ofNat 64 0xc ∨ w' = b + BitVec.ofNat 64 0x15)

/-- The cut points of the body at `b` with initial registers `R` and a measure `k`. -/
def PCM (R : Reg → Word) (b : Word) (k : Nat) (rip rax rdx rdi cf zf : Word) : Prop :=
  let x := (R .rdi).setWidth 32
  let y := (R .rsi).setWidth 32
  let c := (x + y).ult x
  let z := (x + y).setWidth 64
  (rip = b ∧ rdi = R .rdi ∧ k = 12) ∨
  (rip = b + BitVec.ofNat 64 2 ∧ rdx = 0 ∧ rdi = R .rdi ∧ k = 11) ∨
  (rip = b + BitVec.ofNat 64 4 ∧ rdx = 0 ∧ rdi = z ∧ cf = b64 c ∧ k = 10) ∨
  (rip = b + BitVec.ofNat 64 0x16 ∧ rdi = z ∧ c = true ∧ k = 9) ∨
  (rip = b + BitVec.ofNat 64 0x1b ∧ rdx = 1 ∧ rdi = z ∧ c = true ∧ k = 8) ∨
  (rip = b + BitVec.ofNat 64 6 ∧ rdx = b64 c ∧ rdi = z ∧ k = 7) ∨
  (rip = b + BitVec.ofNat 64 8 ∧ rdx = b64 c ∧ rax = z ∧ k = 6) ∨
  (rip = b + BitVec.ofNat 64 0xa ∧ rax = z ∧ zf = b64 (!c) ∧ k = 5) ∨
  (rip = b + BitVec.ofNat 64 0x10 ∧ c = true ∧ k = 4) ∨
  (rip = b + BitVec.ofNat 64 0xc ∧ rax = z ∧ c = false) ∨
  (rip = b + BitVec.ofNat 64 0x15 ∧ rax = 0xffffffff ∧ c = true)

/-- The measured invariant on stores. -/
def JM (f : Frame) (R : Reg → Word) (b : Word) (k : Nat) (s : Store H) : Prop :=
  ∃ rip rax rdx rdi cf zf, Vals s f R rip rax rdx rdi cf zf ∧ PCM R b k rip rax rdx rdi cf zf

theorem ctab_eq (b : Word) : compileTab (satTab b) =
    [(b + BitVec.ofNat 64 0, zero32Code .rdx ++ nextCode 2),
     (b + BitVec.ofNat 64 2, alu32Code .add .rdi .rsi ++ nextCode 2),
     (b + BitVec.ofNat 64 4, jccCode [gget .cf] 0x10 2),
     (b + BitVec.ofNat 64 6, mov32Code .rax .rdi ++ nextCode 2),
     (b + BitVec.ofNat 64 8, test32Code .rdx .rdx ++ nextCode 2),
     (b + BitVec.ofNat 64 0xa, jccCode [gget .zf, c64 1, b64op .xor] 4 2),
     (b + BitVec.ofNat 64 0x10, movI32Code .rax 0xffffffff ++ nextCode 5),
     (b + BitVec.ofNat 64 0x16, movI32Code .rdx 1 ++ nextCode 5),
     (b + BitVec.ofNat 64 0x1b, jmpCode 0xe9 2)] := rfl

theorem zext_mask (z : BitVec 32) : z.setWidth 64 &&& 0xffffffff = z.setWidth 64 := by
  rw [← mov32_val, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]

theorem b64_low (c : Bool) : ((b64 c).setWidth 32 == 0#32) = !c := by cases c <;> rfl

theorem b64_xor1 (t : Bool) : b64 t ^^^ 1 = b64 (!t) := by cases t <;> decide

/-- Addresses at offsets from `b`, as the lookups compare them. -/
theorem off_ne (b : Word) {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (h : x ≠ y) :
    (b + BitVec.ofNat 64 x = b + BitVec.ofNat 64 y) = False := by
  apply propext; constructor
  · intro e; exact h (Silmaril.Sim.Reduce.Loop.off_inj e hx hy)
  · intro e; exact e.elim

theorem add_off (b : Word) (x y : Nat) :
    b + BitVec.ofNat 64 x + BitVec.ofNat 64 y = b + BitVec.ofNat 64 (x + y) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- Lookups at the offsets. -/
theorem addr_self (b c : Word) : (b + c = b) = (c = 0) := propext ⟨fun h => by
  have := congrArg (· - b) h; simpa using this, fun h => by simp [h]⟩

theorem addr_inj (b c d : Word) : (b + c = b + d) = (c = d) := propext ⟨fun h => by
  have := congrArg (· - b) h; simpa [BitVec.add_comm b] using this, fun h => by rw [h]⟩

syntax "sat_lookup " ident : tactic
macro_rules
  | `(tactic| sat_lookup $h) => `(tactic| (
    simp only [ctab_eq, lookupC, add_off, BitVec.add_zero] at $h:ident
    simp (config := { decide := true }) only [addr_self, addr_inj, ite_true, ite_false,
      reduceCtorEq, Option.some.injEq] at $h:ident))

/-- The conclusion of `measured_step` for one entry. -/
private abbrev MStep (f : Frame) (R : Reg → Word) (b : Word) (k : Nat) (s : Store H)
    (code : List Instr) : Prop :=
  ∃ s', Silmaril.Wasm.Logic.Core.exec s f [] code = some (s', f, []) ∧ ∃ k' < k, JM f R b k' s'

set_option maxHeartbeats 1000000 in
private theorem ms0 {R : Reg → Word} {b : Word} {k : Nat} {code : List Instr}
    {rip rax rdx rdi cf zf : Word} (hV : Vals s f R rip rax rdx rdi cf zf)
    (hc : lookupC (compileTab (satTab b)) rip = some code)
    (h : rip = b ∧ rdi = R .rdi ∧ k = 12) :
    MStep f R b k s code := by
  obtain ⟨rfl, rfl, rfl⟩ := h
  sat_lookup hc; subst hc
  obtain ⟨s'', he, hV'⟩ := step0 hV
  exact ⟨s'', he, 11, by omega, _, _, _, _, _, _, hV', .inr (.inl ⟨rfl, rfl, rfl, rfl⟩)⟩

set_option maxHeartbeats 1000000 in
private theorem ms2 {R : Reg → Word} {b : Word} {k : Nat} {code : List Instr}
    {rip rax rdx rdi cf zf : Word} (hV : Vals s f R rip rax rdx rdi cf zf)
    (hc : lookupC (compileTab (satTab b)) rip = some code)
    (h : rip = b + BitVec.ofNat 64 2 ∧ rdx = 0 ∧ rdi = R .rdi ∧ k = 11) :
    MStep f R b k s code := by
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  sat_lookup hc; subst hc
  obtain ⟨s'', he, zf', hV'⟩ := step2 hV
  refine ⟨s'', he, 10, by omega, _, _, _, _, _, _, hV', .inr (.inr (.inl ⟨?_, rfl, rfl, rfl, rfl⟩))⟩
  bv_omega

set_option maxHeartbeats 1000000 in
private theorem ms4 {R : Reg → Word} {b : Word} {k : Nat} {code : List Instr}
    {rip rax rdx rdi cf zf : Word} (hV : Vals s f R rip rax rdx rdi cf zf)
    (hc : lookupC (compileTab (satTab b)) rip = some code)
    (h : rip = b + BitVec.ofNat 64 4 ∧ rdx = 0 ∧ rdi = (((R .rdi).setWidth 32 + (R .rsi).setWidth 32).setWidth 64) ∧ cf = b64 (((R .rdi).setWidth 32 + (R .rsi).setWidth 32).ult ((R .rdi).setWidth 32)) ∧ k = 10) :
    MStep f R b k s code := by
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
  sat_lookup hc; subst hc
  obtain ⟨s'', he, hV'⟩ := step4 hV
  rw [jcc_bits] at hV'
  cases hcc : ((R .rdi).setWidth 32 + (R .rsi).setWidth 32).ult ((R .rdi).setWidth 32)
  · rw [hcc] at hV'
    refine ⟨s'', he, 7, by omega, _, _, _, _, _, _, hV', .inr (.inr (.inr (.inr (.inr (.inl ⟨?_, by simp [hcc, b64], rfl, rfl⟩)))))⟩
    (try simp only [Bool.false_eq_true, ite_false, BitVec.add_zero]); bv_omega
  · rw [hcc] at hV'
    refine ⟨s'', he, 9, by omega, _, _, _, _, _, _, hV', .inr (.inr (.inr (.inl ⟨?_, rfl, hcc, rfl⟩)))⟩
    (try simp only [ite_true]); bv_omega

set_option maxHeartbeats 1000000 in
private theorem ms16 {R : Reg → Word} {b : Word} {k : Nat} {code : List Instr}
    {rip rax rdx rdi cf zf : Word} (hV : Vals s f R rip rax rdx rdi cf zf)
    (hc : lookupC (compileTab (satTab b)) rip = some code)
    (h : rip = b + BitVec.ofNat 64 0x16 ∧ rdi = (((R .rdi).setWidth 32 + (R .rsi).setWidth 32).setWidth 64) ∧ (((R .rdi).setWidth 32 + (R .rsi).setWidth 32).ult ((R .rdi).setWidth 32)) = true ∧ k = 9) :
    MStep f R b k s code := by
  obtain ⟨rfl, rfl, hc1, rfl⟩ := h
  sat_lookup hc; subst hc
  obtain ⟨s'', he, hV'⟩ := step16 hV
  refine ⟨s'', he, 8, by omega, _, _, _, _, _, _, hV', .inr (.inr (.inr (.inr (.inl ⟨?_, rfl, rfl, hc1, rfl⟩))))⟩
  bv_omega

set_option maxHeartbeats 1000000 in
private theorem ms1b {R : Reg → Word} {b : Word} {k : Nat} {code : List Instr}
    {rip rax rdx rdi cf zf : Word} (hV : Vals s f R rip rax rdx rdi cf zf)
    (hc : lookupC (compileTab (satTab b)) rip = some code)
    (h : rip = b + BitVec.ofNat 64 0x1b ∧ rdx = 1 ∧ rdi = (((R .rdi).setWidth 32 + (R .rsi).setWidth 32).setWidth 64) ∧ (((R .rdi).setWidth 32 + (R .rsi).setWidth 32).ult ((R .rdi).setWidth 32)) = true ∧ k = 8) :
    MStep f R b k s code := by
  obtain ⟨rfl, rfl, rfl, hc1, rfl⟩ := h
  sat_lookup hc; subst hc
  obtain ⟨s'', he, hV'⟩ := step1b hV
  refine ⟨s'', he, 7, by omega, _, _, _, _, _, _, hV', .inr (.inr (.inr (.inr (.inr (.inl ⟨?_, by rw [hc1]; rfl, rfl, rfl⟩)))))⟩
  rw [show ((0xe9 : BitVec 8).signExtend 64) = 0xffffffffffffffe9 from rfl]; bv_omega

set_option maxHeartbeats 1000000 in
private theorem ms6 {R : Reg → Word} {b : Word} {k : Nat} {code : List Instr}
    {rip rax rdx rdi cf zf : Word} (hV : Vals s f R rip rax rdx rdi cf zf)
    (hc : lookupC (compileTab (satTab b)) rip = some code)
    (h : rip = b + BitVec.ofNat 64 6 ∧ rdx = b64 (((R .rdi).setWidth 32 + (R .rsi).setWidth 32).ult ((R .rdi).setWidth 32)) ∧ rdi = (((R .rdi).setWidth 32 + (R .rsi).setWidth 32).setWidth 64) ∧ k = 7) :
    MStep f R b k s code := by
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  sat_lookup hc; subst hc
  obtain ⟨s'', he, hV'⟩ := step6 hV
  rw [zext_mask] at hV'
  refine ⟨s'', he, 6, by omega, _, _, _, _, _, _, hV', .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨?_, rfl, rfl, rfl⟩))))))⟩
  bv_omega

set_option maxHeartbeats 1000000 in
private theorem ms8 {R : Reg → Word} {b : Word} {k : Nat} {code : List Instr}
    {rip rax rdx rdi cf zf : Word} (hV : Vals s f R rip rax rdx rdi cf zf)
    (hc : lookupC (compileTab (satTab b)) rip = some code)
    (h : rip = b + BitVec.ofNat 64 8 ∧ rdx = b64 (((R .rdi).setWidth 32 + (R .rsi).setWidth 32).ult ((R .rdi).setWidth 32)) ∧ rax = (((R .rdi).setWidth 32 + (R .rsi).setWidth 32).setWidth 64) ∧ k = 6) :
    MStep f R b k s code := by
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  sat_lookup hc; subst hc
  obtain ⟨s'', he, hV'⟩ := step8 hV
  rw [b64_low] at hV'
  refine ⟨s'', he, 5, by omega, _, _, _, _, _, _, hV', .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨?_, rfl, rfl, rfl⟩)))))))⟩
  bv_omega

set_option maxHeartbeats 1000000 in
private theorem msA {R : Reg → Word} {b : Word} {k : Nat} {code : List Instr}
    {rip rax rdx rdi cf zf : Word} (hV : Vals s f R rip rax rdx rdi cf zf)
    (hc : lookupC (compileTab (satTab b)) rip = some code)
    (h : rip = b + BitVec.ofNat 64 0xa ∧ rax = (((R .rdi).setWidth 32 + (R .rsi).setWidth 32).setWidth 64) ∧ zf = b64 (!(((R .rdi).setWidth 32 + (R .rsi).setWidth 32).ult ((R .rdi).setWidth 32))) ∧ k = 5) :
    MStep f R b k s code := by
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  sat_lookup hc; subst hc
  obtain ⟨s'', he, hV'⟩ := stepA hV
  rw [b64_xor1, Bool.not_not, jcc_bits] at hV'
  cases hcc : ((R .rdi).setWidth 32 + (R .rsi).setWidth 32).ult ((R .rdi).setWidth 32)
  · rw [hcc] at hV'
    refine ⟨s'', he, 0, by omega, _, _, _, _, _, _, hV', .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨?_, rfl, hcc⟩)))))))))⟩
    (try simp only [Bool.false_eq_true, ite_false, BitVec.add_zero]); bv_omega
  · rw [hcc] at hV'
    refine ⟨s'', he, 4, by omega, _, _, _, _, _, _, hV', .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨?_, hcc, rfl⟩))))))))⟩
    (try simp only [ite_true]); bv_omega

set_option maxHeartbeats 1000000 in
private theorem ms10 {R : Reg → Word} {b : Word} {k : Nat} {code : List Instr}
    {rip rax rdx rdi cf zf : Word} (hV : Vals s f R rip rax rdx rdi cf zf)
    (hc : lookupC (compileTab (satTab b)) rip = some code)
    (h : rip = b + BitVec.ofNat 64 0x10 ∧ (((R .rdi).setWidth 32 + (R .rsi).setWidth 32).ult ((R .rdi).setWidth 32)) = true ∧ k = 4) :
    MStep f R b k s code := by
  obtain ⟨rfl, hc1, rfl⟩ := h
  sat_lookup hc; subst hc
  obtain ⟨s'', he, hV'⟩ := step10 hV
  refine ⟨s'', he, 0, by omega, _, _, _, _, _, _, hV', .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (⟨?_, rfl, hc1⟩))))))))))⟩
  bv_omega

set_option maxHeartbeats 1000000 in
private theorem ms_ret {R : Reg → Word} {b : Word} {k : Nat} {code : List Instr}
    {rip : Word} (hc : lookupC (compileTab (satTab b)) rip = some code)
    (h : rip = b + BitVec.ofNat 64 0xc ∨ rip = b + BitVec.ofNat 64 0x15) :
    MStep f R b k s code := by
  rcases h with rfl | rfl
  · sat_lookup hc
  · sat_lookup hc

/-- **Every dispatcher entry evaluates and decreases the measure** (Wasm level). -/
theorem measured_step (R : Reg → Word) (b : Word) :
    ∀ k (s : Store H), JM f R b k s → ∀ w code, gval s f .rip = some (Val.i64 w) →
      lookupC (compileTab (satTab b)) w = some code →
      ∃ s', Silmaril.Wasm.Logic.Core.exec s f [] code = some (s', f, []) ∧
        ∃ k' < k, JM f R b k' s' := by
  rintro k s ⟨rip, rax, rdx, rdi, cf, zf, hV, hpc⟩ w code hw hc
  have hwr : w = rip := val_i64_inj.mp (Option.some.inj (hw.symm.trans hV.2.1))
  have hc' : lookupC (compileTab (satTab b)) rip = some code := hwr ▸ hc
  rcases hpc with h | h | h | h | h | h | h | h | h | h | h
  · exact ms0 hV hc' h
  · exact ms2 hV hc' h
  · exact ms4 hV hc' h
  · exact ms16 hV hc' h
  · exact ms1b hV hc' h
  · exact ms6 hV hc' h
  · exact ms8 hV hc' h
  · exact msA hV hc' h
  · exact ms10 hV hc' h
  · exact ms_ret hc' (.inl h.1)
  · exact ms_ret hc' (.inr h.1)


/-- The measured invariant is a **Wasm ranking** of the dispatcher (termination piece). -/
theorem ranked (R : Reg → Word) (b : Word) :
    Silmaril.Sim.Reduce.Loop.Ranked (compileTab (satTab b)) f (JM (H := H) f R b) := by
  intro k s w code hJ hw hc
  obtain ⟨s', he, k', hk, hJ'⟩ := measured_step R b k s hJ w code hw hc
  exact ⟨s', k', he, hJ', hk⟩

variable {P : Profile} {host : HostSemantics H}

/-- **The Wasm problem of `sat_add_u32` is solved** (every run of the dispatcher from RIP `b`). -/
theorem wasm_solution (b : Word) :
    LProblem (H := H) P host (dispCode (compileTab (satTab b))) (fun _ w => w = b) SatPost := by
  intro s f R w hG hw hb
  obtain ⟨hl, hr, -, ⟨bc, hc⟩, ⟨bz, hz⟩, -, -⟩ := hG
  subst hb
  refine dispatch_hwp _ (fun s' => ∃ k, JM f R w k s') _ ?_
    ⟨12, w, R .rax, R .rdx, R .rdi, b64 bc, b64 bz,
      ⟨hl, hw, hr _, hr _, hr _, hc, hz, fun r _ _ _ => hr r⟩, .inl ⟨rfl, rfl, rfl⟩⟩
  rintro s' ⟨k, hJ⟩
  obtain ⟨rip, rax, rdx, rdi, cf, zf, hV, hpc⟩ := hJ
  refine ⟨rip, hV.2.1, ?_⟩
  cases hlk : lookupC (compileTab (satTab w)) rip with
  | some code =>
    obtain ⟨s'', he, k', -, hJ'⟩ :=
      measured_step R w k s' ⟨rip, rax, rdx, rdi, cf, zf, hV, hpc⟩ rip code hV.2.1 hlk
    exact ⟨s'', he, k', hJ'⟩
  | none =>
    have exit : (rip = w + BitVec.ofNat 64 0xc ∧ rax = ((R .rdi).setWidth 32 + (R .rsi).setWidth 32).setWidth 64 ∧
        ((R .rdi).setWidth 32 + (R .rsi).setWidth 32).ult ((R .rdi).setWidth 32) = false) ∨
        (rip = w + BitVec.ofNat 64 0x15 ∧ rax = 0xffffffff ∧
        ((R .rdi).setWidth 32 + (R .rsi).setWidth 32).ult ((R .rdi).setWidth 32) = true) := by
      rcases hpc with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ |
        ⟨rfl, -⟩ | ⟨rfl, -⟩ | h | h
      all_goals first
        | exact .inl h
        | exact .inr h
        | (exfalso; sat_lookup hlk)
    refine ⟨rfl, fun R' w' hR' hw' => ?_⟩
    have hax := hR' .rax
    rw [hV.2.2.1, Option.some.injEq, val_i64_inj] at hax
    rw [hV.2.1, Option.some.injEq, val_i64_inj] at hw'
    refine ⟨?_, fun r h1 h2 h3 => ?_, ?_⟩
    · rcases exit with ⟨-, rfl, hc0⟩ | ⟨-, rfl, hc1⟩
      · rw [← hax, satAdd, hc0]; rfl
      · rw [← hax, satAdd, hc1]; rfl
    · have h' := hR' r
      rw [hV.2.2.2.2.2.2.2 r h1 h2 h3, Option.some.injEq, val_i64_inj] at h'
      exact h'.symm
    · rcases exit with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact .inl hw'.symm
      · exact .inr hw'.symm

end Silmaril.Sim.ElfVerify.SatAdd
