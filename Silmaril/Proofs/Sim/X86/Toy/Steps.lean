module

public import Silmaril.Sim.X86.Toy.Defs
public import Silmaril.Sim.X86.GM.Thms
public import Silmaril.Sim.X86.SumTo.Thms

/-!
# The toy `f`: the dispatcher entries as straight-line Wasm problems

`TV s f R ip ax di sp bx r12 zf B`: the store's RIP, `rax`, `rdi`, `rsp`, `rbx`, `r12`, ZF and
Wasm memory, the other registers being `R`'s. One lemma per entry of the dispatcher
(`ctab_eq`): its code evaluates to a store with the stated new values (register forms by the
`toy_step` evaluation, stack forms by `Silmaril.Sim.X86.GM.push_wstep` and friends).
-/

@[expose] public section

namespace Silmaril.Sim.X86.Toy

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.X86 (Reg Word)
open Silmaril.Sim.X86.G Silmaril.Sim.X86.GM Silmaril.Sim.X86.Loop
open Silmaril.Wasm.Logic.Core (exec exec_cons exec_nil)

variable {H : Type} {s : Store H} {f : Frame}

/-- The globals and the Wasm memory the toy's code reads and writes. -/
def TV (s : Store H) (f : Frame) (R : Reg → Word) (ip ax di sp bx r12 zf : Word)
    (B : ByteArray) : Prop :=
  Layout s f ∧ gval s f .rip = some (Val.i64 ip) ∧ gval s f (.reg .rax) = some (Val.i64 ax) ∧
    gval s f (.reg .rdi) = some (Val.i64 di) ∧ gval s f (.reg .rsp) = some (Val.i64 sp) ∧
    gval s f (.reg .rbx) = some (Val.i64 bx) ∧ gval s f (.reg .r12) = some (Val.i64 r12) ∧
    gval s f .zf = some (Val.i64 zf) ∧
    (∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsp → r ≠ .rbx → r ≠ .r12 →
      gval s f (.reg r) = some (Val.i64 (R r))) ∧ wbytes s f = some B ∧ 40 ≤ B.size

theorem ctab_eq (b sp : Word) : compileTabM (toyWin sp) (toyTab b) =
    [(b, [c64 ((0 : BitVec 32).signExtend 64), gset (.reg .rax)] ++ nextCode 7),
     (b + 0x07, testCode .rdi .rdi ++ nextCode 3),
     (b + 0x0a, jccCode [gget .zf] 0x09 2),
     (b + 0x0c, aluCode .add .rax .rdi ++ nextCode 3),
     (b + 0x0f, aluICode .sub .rdi ((1 : BitVec 8).signExtend 64) ++ nextCode 4),
     (b + 0x13, jmpCode 0xf2 2),
     (b + 0x15, loadCode (toyWin sp) [gget (.reg .rsp)] ++ [gget (.reg .rsp), c64 8, b64op .add,
        gset (.reg .rsp), gset .rip]),
     (b + 0x16, [gget (.reg .rdi), gset (.reg .rax)] ++ nextCode 3),
     (b + 0x19, aluCode .add .rax .rax ++ nextCode 3),
     (b + 0x1c, loadCode (toyWin sp) [gget (.reg .rsp)] ++ [gget (.reg .rsp), c64 8, b64op .add,
        gset (.reg .rsp), gset .rip]),
     (b + 0x1d, storeCode (toyWin sp) rspDown [gget (.reg .rbx)] ++ rspDown ++ [gset (.reg .rsp)] ++
        nextCode 1),
     (b + 0x1e, storeCode (toyWin sp) rspDown [gget (.reg .r12)] ++ rspDown ++ [gset (.reg .rsp)] ++
        nextCode 2),
     (b + 0x20, aluICode .sub .rsp ((8 : BitVec 8).signExtend 64) ++ nextCode 4),
     (b + 0x24, [gget (.reg .rsi), gset (.reg .rbx)] ++ nextCode 3),
     (b + 0x27, storeCode (toyWin sp) rspDown [gget .rip, c64 (BitVec.ofNat 64 5), b64op .add] ++
        rspDown ++ [gset (.reg .rsp), gget .rip,
        c64 (BitVec.ofNat 64 5 + (0xffffffd4 : BitVec 32).signExtend 64), b64op .add, gset .rip]),
     (b + 0x2c, [gget (.reg .rax), gset (.reg .r12)] ++ nextCode 3),
     (b + 0x2f, [gget (.reg .rbx), gset (.reg .rdi)] ++ nextCode 3),
     (b + 0x32, storeCode (toyWin sp) rspDown [gget .rip, c64 (BitVec.ofNat 64 5), b64op .add] ++
        rspDown ++ [gset (.reg .rsp), gget .rip,
        c64 (BitVec.ofNat 64 5 + (0xffffffdf : BitVec 32).signExtend 64), b64op .add, gset .rip]),
     (b + 0x37, aluCode .add .rax .r12 ++ nextCode 3),
     (b + 0x3a, aluICode .add .rsp ((8 : BitVec 8).signExtend 64) ++ nextCode 4),
     (b + 0x3e, loadCode (toyWin sp) [gget (.reg .rsp)] ++ [gget (.reg .rsp), c64 8, b64op .add,
        gset (.reg .rsp), gset (.reg .r12)] ++ nextCode 2),
     (b + 0x40, loadCode (toyWin sp) [gget (.reg .rsp)] ++ [gget (.reg .rsp), c64 8, b64op .add,
        gset (.reg .rsp), gset (.reg .rbx)] ++ nextCode 1),
     (b + 0x41, loadCode (toyWin sp) [gget (.reg .rsp)] ++ [gget (.reg .rsp), c64 8, b64op .add,
        gset (.reg .rsp), gset .rip])] := rfl

/-- Evaluate a register-form entry on a store given by `TV`. -/
syntax "toy_step" : tactic
macro_rules
  | `(tactic| toy_step) => `(tactic| (
    simp (maxDischargeDepth := 20) (contextual := true) only [aluCode, carryCode, overflowCode,
      zeroCode, msbCode, notCode, aluWasm, nextCode, testCode, jccCode, jmpCode,
      aluICode, List.cons_append, List.nil_append, exec_cons, exec_nil,
      exec1_gget, Layout.upd, Option.map_some, exec1_c64, exec1_add, exec1_sub,
      exec1_and, exec1_or, exec1_xor, exec1_shr63, exec1_gset, gval_upd, reduceCtorEq, ite_false,
      ite_true, Option.some.injEq, Prod.mk.injEq, and_true, exists_eq_left', TV, true_and,
      Loc.reg.injEq, val_i64_inj, BitVec.and_self, exists_eq', ne_eq, not_false_eq_true,
      implies_true, wbytes_upd, Silmaril.Sim.X86.SumTo.zf_val, *] <;>
    first | rfl | exact ⟨rfl, rfl⟩ | exact ⟨_, rfl, rfl⟩ | exact ⟨_, rfl, rfl, rfl⟩ |
      exact ⟨rfl, Silmaril.Sim.X86.SumTo.zf_val _⟩ | exact ⟨_, rfl⟩ | skip))

section Reg

variable {R : Reg → Word} {ip ax di sp bx r12 zf : Word} {B : ByteArray}

theorem st_mov0 (h : TV s f R ip ax di sp bx r12 zf B) :
    ∃ s', exec s f [] ([c64 ((0 : BitVec 32).signExtend 64), gset (.reg .rax)] ++ nextCode 7) =
      some (s', f, []) ∧ TV s' f R (ip + 7) 0 di sp bx r12 zf B := by
  obtain ⟨hl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  toy_step

theorem st_test (h : TV s f R ip ax di sp bx r12 zf B) :
    ∃ s', exec s f [] (testCode .rdi .rdi ++ nextCode 3) = some (s', f, []) ∧
      TV s' f R (ip + 3) ax di sp bx r12 (b64 (di == 0)) B := by
  obtain ⟨hl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  toy_step

theorem st_je (h : TV s f R ip ax di sp bx r12 zf B) :
    ∃ s', exec s f [] (jccCode [gget .zf] 0x09 2) = some (s', f, []) ∧
      TV s' f R (ip + 2 + ((0 - zf) &&& 9)) ax di sp bx r12 zf B := by
  obtain ⟨hl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  toy_step

theorem st_add_rax_rdi (h : TV s f R ip ax di sp bx r12 zf B) :
    ∃ s', exec s f [] (aluCode .add .rax .rdi ++ nextCode 3) = some (s', f, []) ∧
      ∃ zf', TV s' f R (ip + 3) (ax + di) di sp bx r12 zf' B := by
  obtain ⟨hl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  toy_step

theorem st_sub_rdi (h : TV s f R ip ax di sp bx r12 zf B) :
    ∃ s', exec s f [] (aluICode .sub .rdi ((1 : BitVec 8).signExtend 64) ++ nextCode 4) =
      some (s', f, []) ∧ ∃ zf', TV s' f R (ip + 4) ax (di - 1) sp bx r12 zf' B := by
  obtain ⟨hl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  toy_step

theorem st_jmp (h : TV s f R ip ax di sp bx r12 zf B) :
    ∃ s', exec s f [] (jmpCode 0xf2 2) = some (s', f, []) ∧
      TV s' f R (ip + (2 + 0xfffffffffffffff2)) ax di sp bx r12 zf B := by
  obtain ⟨hl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  toy_step

theorem st_mov_rax_rdi (h : TV s f R ip ax di sp bx r12 zf B) :
    ∃ s', exec s f [] ([gget (.reg .rdi), gset (.reg .rax)] ++ nextCode 3) = some (s', f, []) ∧
      TV s' f R (ip + 3) di di sp bx r12 zf B := by
  obtain ⟨hl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  toy_step

theorem st_add_rax_rax (h : TV s f R ip ax di sp bx r12 zf B) :
    ∃ s', exec s f [] (aluCode .add .rax .rax ++ nextCode 3) = some (s', f, []) ∧
      ∃ zf', TV s' f R (ip + 3) (ax + ax) di sp bx r12 zf' B := by
  obtain ⟨hl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  toy_step

theorem st_sub_rsp (h : TV s f R ip ax di sp bx r12 zf B) :
    ∃ s', exec s f [] (aluICode .sub .rsp ((8 : BitVec 8).signExtend 64) ++ nextCode 4) =
      some (s', f, []) ∧ ∃ zf', TV s' f R (ip + 4) ax di (sp - 8) bx r12 zf' B := by
  obtain ⟨hl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  toy_step

theorem st_add_rsp (h : TV s f R ip ax di sp bx r12 zf B) :
    ∃ s', exec s f [] (aluICode .add .rsp ((8 : BitVec 8).signExtend 64) ++ nextCode 4) =
      some (s', f, []) ∧ ∃ zf', TV s' f R (ip + 4) ax di (sp + 8) bx r12 zf' B := by
  obtain ⟨hl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  toy_step

theorem st_mov_rbx_rsi (h : TV s f R ip ax di sp bx r12 zf B) :
    ∃ s', exec s f [] ([gget (.reg .rsi), gset (.reg .rbx)] ++ nextCode 3) = some (s', f, []) ∧
      TV s' f R (ip + 3) ax di sp (R .rsi) r12 zf B := by
  obtain ⟨hl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  have hrsi := h8 .rsi (by decide) (by decide) (by decide) (by decide) (by decide)
  toy_step

theorem st_mov_r12_rax (h : TV s f R ip ax di sp bx r12 zf B) :
    ∃ s', exec s f [] ([gget (.reg .rax), gset (.reg .r12)] ++ nextCode 3) = some (s', f, []) ∧
      TV s' f R (ip + 3) ax di sp bx ax zf B := by
  obtain ⟨hl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  toy_step

theorem st_mov_rdi_rbx (h : TV s f R ip ax di sp bx r12 zf B) :
    ∃ s', exec s f [] ([gget (.reg .rbx), gset (.reg .rdi)] ++ nextCode 3) = some (s', f, []) ∧
      TV s' f R (ip + 3) ax bx sp bx r12 zf B := by
  obtain ⟨hl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  toy_step

theorem st_add_rax_r12 (h : TV s f R ip ax di sp bx r12 zf B) :
    ∃ s', exec s f [] (aluCode .add .rax .r12 ++ nextCode 3) = some (s', f, []) ∧
      ∃ zf', TV s' f R (ip + 3) (ax + r12) di sp bx r12 zf' B := by
  obtain ⟨hl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  toy_step

end Reg

section Stack

variable {R : Reg → Word} {ip ax di sp bx r12 zf : Word} {B : ByteArray}

theorem TV.keep {s' : Store H} (h : TV s f R ip ax di sp bx r12 zf B) (hl' : Layout s' f)
    (hS : Same s s' f (SPR .rip)) {ip' sp' : Word} {B' : ByteArray}
    (hsp : gval s' f (.reg .rsp) = some (Val.i64 sp')) (hip : gval s' f .rip = some (Val.i64 ip'))
    (hB : wbytes s' f = some B') (hsz : 40 ≤ B'.size) : TV s' f R ip' ax di sp' bx r12 zf B' := by
  obtain ⟨hl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  refine ⟨hl', hip, ?_, ?_, hsp, ?_, ?_, ?_, fun r a b c d e => ?_, hB, hsz⟩
  all_goals first
    | (rwa [hS _ (by simp [SPR])])
    | (rw [hS _ (by simp [SPR]; tauto)]; exact h8 r a b c d e)

theorem TV.keepR {s' : Store H} (h : TV s f R ip ax di sp bx r12 zf B) (hl' : Layout s' f)
    {X : Reg} (hX : X = .rbx ∨ X = .r12) (hS : Same s s' f (SPR (.reg X))) {ip' sp' v : Word}
    (hsp : gval s' f (.reg .rsp) = some (Val.i64 sp')) (hip : gval s' f .rip = some (Val.i64 ip'))
    (hv : gval s' f (.reg X) = some (Val.i64 v)) (hB : wbytes s' f = some B) :
    TV s' f R ip' ax di sp' (if X = .rbx then v else bx) (if X = .r12 then v else r12) zf B := by
  obtain ⟨hl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  rcases hX with rfl | rfl
  · refine ⟨hl', hip, ?_, ?_, hsp, by simpa using hv, ?_, ?_, fun r a b c d e => ?_, hB, h10⟩
    all_goals first
      | (rwa [hS _ (by simp [SPR])])
      | (rw [hS _ (by simp [SPR]; tauto)]; exact h8 r a b c d e)
  · refine ⟨hl', hip, ?_, ?_, hsp, ?_, by simpa using hv, ?_, fun r a b c d e => ?_, hB, h10⟩
    all_goals first
      | (rwa [hS _ (by simp [SPR])])
      | (rw [hS _ (by simp [SPR]; tauto)]; exact h8 r a b c d e)

end Stack

end Silmaril.Sim.X86.Toy
