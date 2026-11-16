module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.QuoteExit

/-! # GNU `sha256sum`: `quotef`'s exit, the returns

`0x6614` (`buffer[len] = 0`), `0x6279` (guard), `0x628c` (return `len`), `0x6859` (`len < 256`),
`0x68c7` (`errno` restored, return `slot0`), `0x6994` (guard), `0x69a3` (return).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace Silmaril.Elf.Link.Dyn.Sha256sum

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Cert
open Silmaril.Elf.Link.Dyn.Streams

variable {W : World} {b R : Word} {Q : PState → Prop} {c : PState}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- `0x6614`: `buffer[len] = 0`. -/
theorem qx6614 (hd : c.g.done = none) (hC : QC W b c.m.memory 0x6614 quoteX6Text)
    (hrip : c.m.core.rip = b + 0x6614#64) {L : Word} (hr10 : c.m.core.read .r10 = b + 0xa060#64)
    (hr11 : c.m.core.read .r11 = L) (hw : c.m.memory.Permitted .write (b + 0xa060#64 + L).toNat 1)
    (k : ∀ c1 : State, c1.rip = b + 0x6279#64 → (∀ r, c1.read r = c.m.core.read r) →
      c1.fsBase = c.m.core.fsBase →
      MustQ W Q ⟨⟨c1, storeMem c.m.memory (b + 0xa060#64 + L) 1 0#64⟩, c.g⟩) : MustQ W Q c := by
  refine must_blkX_at blk6614 blk6614_ok hd hC.img hC.ld hC.ro (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp [blk6614, hr10, hr11]
  · refine k _ ?_ (fun r => state_read_other (by simp)) (state_fs _ _)
    blk_simp [blk6614, hrip]; bv_omega
  · exact hw

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- `0x6279`: the stack guard is intact: to `0x628c`. -/
theorem qx6279 (hd : c.g.done = none) (hC : QC W b c.m.memory 0x6220 quoteX5Text)
    (hrip : c.m.core.rip = b + 0x6279#64) (hbp : c.m.core.read .rbp = R - 0xd8#64) {g : Word}
    (h110 : loadN c.m.memory (R - 0x110#64) 8 = some g)
    (hg : loadN c.m.memory (c.m.core.fsBase + 0x28#64) 8 = some g)
    (k : ∀ c1 : State, c1.rip = b + 0x628c#64 → (∀ r, r ≠ .rax → c1.read r = c.m.core.read r) →
      c1.fsBase = c.m.core.fsBase → MustQ W Q ⟨⟨c1, c.m.memory⟩, c.g⟩) : MustQ W Q c := by
  refine must_blkX_at blk6279 blk6279_ok hd hC.img hC.ld hC.ro (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp [blk6279, hbp, bsub_add, Nat.reduceAdd, Nat.reduceMod, Nat.reducePow, Nat.reduceSub]
  all_goals try qx_side
  · rename_i v0 h0 v1 h1 b2 h2
    simp only [hbp, bsub_add, Nat.reduceAdd, Nat.reduceMod, Nat.reducePow, Nat.reduceSub] at h0
    rw [h110] at h0; cases h0
    rw [hg] at h1; cases h1
    cases b2
    swap; · exact absurd h2 (by simp [Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.AluOp.flagsN,
      Silmaril.X86.Ext.subFlagsN, Silmaril.X86.Ext.isZeroN, Silmaril.X86.Ext.kNot])
    refine k _ ?_ (fun r h1 => state_read_other (by simp [h1])) (state_fs _ _)
    blk_simp [blk6279, hrip, ripadd, Nat.reduceAdd, sel0]
  · exact ⟨_, hg⟩
  · simp only [h110]; exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `0x628c`: `quotearg_buffer_restyled` returns `len`. -/
theorem qx628c (hd : c.g.done = none) (hC : QC W b c.m.memory 0x6220 quoteX5Text)
    (hrip : c.m.core.rip = b + 0x628c#64) (hsp : c.m.core.read .rsp = R - 0x1c8#64) {ea : Word}
    (h100 : loadN c.m.memory (R - 0x100#64) 8 = some ea)
    (hf8 : loadN c.m.memory (R - 0xf8#64) 8 = some (R - 0x48#64))
    (hf0 : loadN c.m.memory (R - 0xf0#64) 8 = some (b + 0xa060#64))
    (he8 : loadN c.m.memory (R - 0xe8#64) 8 = some 256#64)
    (he0 : loadN c.m.memory (R - 0xe0#64) 8 = some (b + 0xa020#64))
    (hd8 : loadN c.m.memory (R - 0xd8#64) 8 = some (R - 0x58#64))
    (hd0 : loadN c.m.memory (R - 0xd0#64) 8 = some (b + 0x6859#64))
    (k : ∀ c1 : State, c1.rip = b + 0x6859#64 → c1.read .rsp = R - 0xc8#64 → c1.read .rbp = R - 0x58#64 →
      c1.read .rbx = ea → c1.read .r12 = R - 0x48#64 → c1.read .r13 = b + 0xa060#64 →
      c1.read .r14 = 256#64 → c1.read .r15 = b + 0xa020#64 → c1.read .rax = c.m.core.read .r11 →
      c1.fsBase = c.m.core.fsBase → MustQ W Q ⟨⟨c1, c.m.memory⟩, c.g⟩) : MustQ W Q c := by
  refine must_blkX_at blk628c blk628c_ok hd hC.img hC.ld hC.ro (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp [blk628c, hsp, bsub_add, Nat.reduceAdd, Nat.reduceMod, Nat.reducePow, Nat.reduceSub]
  · rename_i v0 h0 v1 h1 v2 h2 v3 h3 v4 h4 v5 h5 v6 h6
    simp only [hsp, bsub_add, Nat.reduceAdd, Nat.reduceMod, Nat.reducePow, Nat.reduceSub] at h0 h1 h2 h3 h4 h5 h6
    rw [pop_of_loadN h100] at h0; cases h0
    rw [pop_of_loadN hf8] at h1; cases h1
    rw [pop_of_loadN hf0] at h2; cases h2
    rw [pop_of_loadN he8] at h3; cases h3
    rw [pop_of_loadN he0] at h4; cases h4
    rw [pop_of_loadN hd8] at h5; cases h5
    rw [pop_of_loadN hd0] at h6; cases h6
    refine k _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (state_fs _ _)
    all_goals blk_simp [blk628c, hsp]
    bv_omega
  all_goals exact ⟨_, pop_of_loadN ‹_›⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- `0x6859`: the two stack arguments popped, `len < 256`: to `0x68c7`. -/
theorem qx6859 (hd : c.g.done = none) (hC : QC W b c.m.memory 0x681c quoteX7Text)
    (hrip : c.m.core.rip = b + 0x6859#64) (hsp : c.m.core.read .rsp = R - 0xc8#64)
    (hc8 : loadN c.m.memory (R - 0xc8#64) 8 = some 0#64) (hc0 : loadN c.m.memory (R - 0xc0#64) 8 = some 0#64)
    (hlt : (c.m.core.read .rax).toNat < (c.m.core.read .r14).toNat)
    (k : ∀ c1 : State, c1.rip = b + 0x68c7#64 → c1.read .rsp = R - 0xb8#64 →
      (∀ r, r ≠ .rcx → r ≠ .rsp → r ≠ .rsi → c1.read r = c.m.core.read r) →
      c1.fsBase = c.m.core.fsBase → MustQ W Q ⟨⟨c1, c.m.memory⟩, c.g⟩) : MustQ W Q c := by
  refine must_blkX_at blk6859 blk6859_ok hd hC.img hC.ld hC.ro (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp [blk6859, hsp, bsub_add, Nat.reduceAdd, Nat.reduceMod, Nat.reducePow, Nat.reduceSub]
  all_goals try qx_side
  · rename_i v0 h0 v1 h1 b2 h2
    have e2 : b2 = true := by
      simp only [Silmaril.X86.Ext.AluOp.flagsN, BitVec.setWidth_eq] at h2
      rw [eval_b_sub] at h2
      have : (c.m.core.read .rax).ult (c.m.core.read .r14) = true := by
        simp only [BitVec.ult, decide_eq_true_eq]; exact hlt
      rw [this] at h2; exact (Option.some.inj h2).symm
    subst e2
    refine k _ ?_ ?_ ?_ (state_fs _ _)
    · blk_simp [blk6859, hrip, ripadd, Nat.reduceAdd, sel1]
    · blk_simp [blk6859, hsp]; bv_omega
    · intro r h1 h2 h3; exact state_read_other (by simp [h1, h2, h3])
  · rename_i v0 h0
    simp only [hsp, bsub_add, Nat.reduceAdd, Nat.reduceMod, Nat.reducePow, Nat.reduceSub] at h0 ⊢
    exact ⟨_, pop_of_loadN hc0⟩
  · exact ⟨_, pop_of_loadN hc8⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `0x68c7`: `errno` written back (the bytes it holds), `quotearg_n_options` returns `slot0`. -/
theorem qx68c7 (hd : c.g.done = none) (hC : QC W b c.m.memory 0x681c quoteX7Text)
    (hrip : c.m.core.rip = b + 0x68c7#64) (hbp : c.m.core.read .rbp = R - 0x58#64) {ea e4 : Word}
    (hbx : c.m.core.read .rbx = ea) (h94 : loadN c.m.memory (R - 0x94#64) 4 = some e4)
    (hrb : c.m.memory.readBytes ea.toNat 4 = some (Silmaril.X86.Ext.leBytes e4 4))
    (hw : c.m.memory.Permitted .write ea.toNat 4) (hea : ea.toNat + 4 + 2048 ≤ R.toNat) {x80 x78 x70 x68 x60 x58 : Word}
    (h80 : loadN c.m.memory (R - 0x80#64) 8 = some x80) (h78 : loadN c.m.memory (R - 0x78#64) 8 = some x78)
    (h70 : loadN c.m.memory (R - 0x70#64) 8 = some x70) (h68 : loadN c.m.memory (R - 0x68#64) 8 = some x68)
    (h60 : loadN c.m.memory (R - 0x60#64) 8 = some x60) (h58 : loadN c.m.memory (R - 0x58#64) 8 = some x58)
    (h50 : loadN c.m.memory (R - 0x50#64) 8 = some (b + 0x6994#64))
    (k : ∀ c1 : State, c1.rip = b + 0x6994#64 → c1.read .rsp = R - 0x48#64 → c1.read .rbp = x58 →
      c1.read .rbx = x80 → c1.read .r12 = x78 → c1.read .r13 = x70 → c1.read .r14 = x68 →
      c1.read .r15 = x60 → c1.read .rax = c.m.core.read .r13 → c1.fsBase = c.m.core.fsBase →
      MustQ W Q ⟨⟨c1, storeMem c.m.memory ea 4 e4⟩, c.g⟩) : MustQ W Q c := by
  have hz : (e4.setWidth 32).setWidth 64 = e4 := zext_small (loadN_lt h94) (by omega)
  have hS : Keeps (fun _ => True) c.m.memory (storeMem c.m.memory ea 4 e4) := storeMem_same hrb
  have hp : ∀ {a v : Word}, loadN c.m.memory a 8 = some v →
      ((storeMem c.m.memory ea 4 e4).readBytes a.toNat 8).bind Silmaril.X86.wordOfBytes? = some v := by
    intro a v h
    rw [hS.readBytes fun _ _ => trivial]; exact pop_of_loadN h
  have hp' : ∀ (x : Word) {d : Nat} {v : Word}, d ≤ 0x100 → loadN c.m.memory (R - BitVec.ofNat 64 d) 8 = some v →
      ((storeMem c.m.memory ea 4 x).readBytes (R - BitVec.ofNat 64 d).toNat 8).bind Silmaril.X86.wordOfBytes? =
        some v := by
    intro x d v hd' h
    rw [storeMem_read_ne (by rw [bsub_toNat (by omega)]; omega)]; exact pop_of_loadN h
  refine must_blkX_at blk68c7 blk68c7_ok hd hC.img hC.ld hC.ro (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp [blk68c7, hbp, hbx, bsub_add, Nat.reduceAdd, Nat.reduceMod, Nat.reducePow, Nat.reduceSub]
  · rename_i v0 h0 v1 h1 v2 h2 v3 h3 v4 h4 v5 h5 v6 h6 v7 h7
    simp only [hbp, hbx, bsub_add, Nat.reduceAdd, Nat.reduceMod, Nat.reducePow, Nat.reduceSub] at h0
    rw [h94] at h0; cases h0
    simp only [hz] at h1 h2 h3 h4 h5 h6 h7 ⊢
    simp only [hbp, hbx, bsub_add, Nat.reduceAdd, Nat.reduceMod, Nat.reducePow, Nat.reduceSub] at h1 h2 h3 h4 h5 h6 h7
    rw [hp h80] at h1; cases h1
    rw [hp h78] at h2; cases h2
    rw [hp h70] at h3; cases h3
    rw [hp h68] at h4; cases h4
    rw [hp h60] at h5; cases h5
    rw [hp h58] at h6; cases h6
    rw [hp h50] at h7; cases h7
    refine k _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (state_fs _ _)
    all_goals blk_simp [blk68c7, hbp]
    bv_omega
  all_goals try simp only [hbx, hz]
  all_goals first
    | exact ⟨_, hp' _ (by omega) h80⟩
    | exact ⟨_, hp' _ (by omega) h78⟩
    | exact ⟨_, hp' _ (by omega) h70⟩
    | exact ⟨_, hp' _ (by omega) h68⟩
    | exact ⟨_, hp' _ (by omega) h60⟩
    | exact ⟨_, hp' _ (by omega) h58⟩
    | exact ⟨_, hp' _ (by omega) h50⟩
    | exact ⟨_, h94⟩
    | exact hw

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- `0x6994`: `quotef`'s guard check: to `0x69a3`. -/
theorem qx6994 (hd : c.g.done = none) (hC : QC W b c.m.memory 0x681c quoteX7Text)
    (hrip : c.m.core.rip = b + 0x6994#64) (hbp : c.m.core.read .rbp = R - 8#64) {g : Word}
    (h10 : loadN c.m.memory (R - 0x10#64) 8 = some g)
    (hg : loadN c.m.memory (c.m.core.fsBase + 0x28#64) 8 = some g)
    (k : ∀ c1 : State, c1.rip = b + 0x69a3#64 → (∀ r, r ≠ .rdx → c1.read r = c.m.core.read r) →
      c1.fsBase = c.m.core.fsBase → MustQ W Q ⟨⟨c1, c.m.memory⟩, c.g⟩) : MustQ W Q c := by
  refine must_blkX_at blk6994 blk6994_ok hd hC.img hC.ld hC.ro (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp [blk6994, hbp, bsub_add, Nat.reduceAdd, Nat.reduceMod, Nat.reducePow, Nat.reduceSub]
  all_goals try qx_side
  · rename_i v0 h0 v1 h1 b2 h2
    simp only [hbp, bsub_add, Nat.reduceAdd, Nat.reduceMod, Nat.reducePow, Nat.reduceSub] at h0
    rw [h10] at h0; cases h0
    rw [hg] at h1; cases h1
    cases b2
    swap; · exact absurd h2 (by simp [Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.AluOp.flagsN,
      Silmaril.X86.Ext.subFlagsN, Silmaril.X86.Ext.isZeroN, Silmaril.X86.Ext.kNot])
    refine k _ ?_ (fun r h1 => state_read_other (by simp [h1])) (state_fs _ _)
    blk_simp [blk6994, hrip, ripadd, Nat.reduceAdd, sel0]
  · exact ⟨_, hg⟩
  · simp only [h10]; exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- `0x69a3`: `leave; ret` of `quotef`. -/
theorem qx69a3 (hd : c.g.done = none) (hC : QC W b c.m.memory 0x681c quoteX7Text)
    (hrip : c.m.core.rip = b + 0x69a3#64) (hbp : c.m.core.read .rbp = R - 8#64) {rb ra : Word}
    (h8 : loadN c.m.memory (R - 8#64) 8 = some rb) (h0 : loadN c.m.memory R 8 = some ra)
    (k : ∀ c1 : State, c1.rip = ra → c1.read .rsp = R + 8#64 → c1.read .rbp = rb →
      (∀ r, r ≠ .rsp → r ≠ .rbp → c1.read r = c.m.core.read r) →
      c1.fsBase = c.m.core.fsBase → MustQ W Q ⟨⟨c1, c.m.memory⟩, c.g⟩) : MustQ W Q c := by
  have e8 : R - 8#64 + 8#64 = R := by bv_omega
  refine must_blkX_at blk69a3 blk69a3_ok hd hC.img hC.ld hC.ro (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp [blk69a3, hbp, e8, BitVec.add_zero]
  · rename_i v0 h0' v1 h1'
    simp only [hbp, e8] at h0' h1'
    rw [pop_of_loadN h8] at h0'; cases h0'
    rw [pop_of_loadN h0] at h1'; cases h1'
    refine k _ ?_ ?_ ?_ ?_ (state_fs _ _)
    · blk_simp [blk69a3]
    · blk_simp [blk69a3, hbp]; bv_omega
    · blk_simp [blk69a3]
    · intro r h1 h2; exact state_read_other (by simp [h1, h2])
  · exact ⟨_, pop_of_loadN h0⟩
  · exact ⟨_, pop_of_loadN h8⟩

end Silmaril.Elf.Link.Dyn.Sha256sum
