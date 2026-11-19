module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.QuoteProRun
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.QuoteIterBlk

/-! # GNU `sha256sum`: `quotef`'s exit (`Task.quoteExit`), the blocks

From the loop head with all `p.length` bytes copied: the NUL ends the loop (`0x50cd`, `0x50d9`),
`0x5f99`/`0x5faa` (not `shell_always` with an empty buffer), `0x6220`–`0x6270` (no closing quote,
`len < 256`), `0x6614` (`buffer[len] = 0`), `0x6279` (guard), `0x628c` (return `len`), `0x6859`
(`len < 256`), `0x68c7` (`errno` restored), `0x6994` (guard), `0x69a3` (return).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

set_option linter.unusedSimpArgs false

namespace Silmaril.Elf.Link.Dyn.Sha256sum

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Cert
open Silmaril.Elf.Link.Dyn.Streams

theorem pop_of_loadN {m : Memory} {a v : Word} (h : loadN m a 8 = some v) :
    (m.readBytes a.toNat 8).bind Silmaril.X86.wordOfBytes? = some v := by
  rw [readBytes_of_loadN' h (le_refl _), Silmaril.X86.Ext.leBytes_eight]
  simp

macro "qx_side" : tactic => `(tactic| first
  | exact eval_some (defined_alu _ _ _ _) _
  | exact eval_some (defined_logic _) _)

variable {W : World} {b R : Word} {Q : PState → Prop} {c : PState}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- `0x50cd`: the byte at `name + len` is the NUL. -/
theorem qx50cd (hd : c.g.done = none) (hC : QC W b c.m.memory 0x4f50 quoteX0Text)
    (hrip : c.m.core.rip = b + 0x50cd#64) (hbp : c.m.core.read .rbp = R - 0xd8#64) {nm : Word}
    (hnm : loadN c.m.memory (R - 0x148#64) 8 = some nm)
    (hc : loadN c.m.memory (nm + c.m.core.read .rbx) 1 = some 0#64)
    (k : ∀ c1 : State, c1.rip = b + 0x50d9#64 → (c1.read .r10).setWidth 8 = 0#8 →
      (∀ r, r ≠ .rax → r ≠ .r10 → c1.read r = c.m.core.read r) → c1.fsBase = c.m.core.fsBase →
      MustQ W Q ⟨⟨c1, c.m.memory⟩, c.g⟩) : MustQ W Q c := by
  refine must_blkX_at blk50cd blk50cd_ok hd hC.img hC.ld hC.ro (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp [blk50cd, hbp, bsub_add, Nat.reduceAdd, Nat.reduceMod, Nat.reducePow, Nat.reduceSub]
  all_goals try qx_side
  · rename_i v0 h0 v1 h1 b2 h2
    simp only [hbp, bsub_add, Nat.reduceAdd, Nat.reduceMod, Nat.reducePow, Nat.reduceSub] at h0
    rw [hnm] at h0; cases h0
    rw [hc] at h1; cases h1
    cases b2
    swap; · exact absurd h2 (by decide)
    refine k _ ?_ ?_ ?_ (state_fs _ _)
    · blk_simp [blk50cd, hrip, ripadd, Nat.reduceAdd]
    · blk_simp [blk50cd]; rw [qi_m8]; decide
    · intro r h1 h2; exact state_read_other (by simp [h1, h2])
  · rename_i v0 h0
    simp only [hbp, bsub_add, Nat.reduceAdd, Nat.reduceMod, Nat.reducePow, Nat.reduceSub] at h0
    rw [hnm] at h0; cases h0; exact ⟨_, hc⟩
  · exact ⟨_, hnm⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- `0x50d9`: the loop ends (`je 0x5f99`). -/
theorem qx50d9 (hd : c.g.done = none) (hC : QC W b c.m.memory 0x4f50 quoteX0Text)
    (hrip : c.m.core.rip = b + 0x50d9#64) (hr10 : (c.m.core.read .r10).setWidth 8 = 0#8)
    (k : ∀ c1 : State, c1.rip = b + 0x5f99#64 → (∀ r, c1.read r = c.m.core.read r) →
      c1.fsBase = c.m.core.fsBase → MustQ W Q ⟨⟨c1, c.m.memory⟩, c.g⟩) : MustQ W Q c := by
  refine must_blkX_at blk50d9 blk50d9_ok hd hC.img hC.ld hC.ro (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp [blk50d9]
  all_goals try qx_side
  rename_i b0 h0
  have e0 : b0 = true := qi_bool h0 (by rw [hr10]; decide)
  subst e0
  refine k _ ?_ (fun r => state_read_other (by simp)) (state_fs _ _)
  blk_simp [blk50d9, hrip, ripadd, Nat.reduceAdd, sel1]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- `0x5f99`: `shell_always` (style 2) and `len ≠ 0`: the flags give `je` taken. -/
theorem qx5f99 (hd : c.g.done = none) (hC : QC W b c.m.memory 0x5f99 quoteX4Text)
    (hrip : c.m.core.rip = b + 0x5f99#64) (hbp : c.m.core.read .rbp = R - 0xd8#64) {L : Word}
    (h134 : loadN c.m.memory (R - 0x134#64) 4 = some 2#64) (h130 : loadN c.m.memory (R - 0x130#64) 8 = some L)
    (hL : L ≠ 0#64)
    (k : ∀ c1 : State, c1.rip = b + 0x5faa#64 → Silmaril.X86.Ext.Cond.eval c1.flags .e = some true →
      (∀ r, r ≠ .rax → r ≠ .rdx → c1.read r = c.m.core.read r) →
      c1.fsBase = c.m.core.fsBase → MustQ W Q ⟨⟨c1, c.m.memory⟩, c.g⟩) : MustQ W Q c := by
  refine must_blkX_at blk5f99 blk5f99_ok hd hC.img hC.ld hC.ro (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp [blk5f99, hbp, bsub_add, Nat.reduceAdd, Nat.reduceMod, Nat.reducePow, Nat.reduceSub]
  all_goals try qx_side
  · rename_i v0 h0 b1 h1 v2 h2 b3 h3
    simp only [hbp, bsub_add, Nat.reduceAdd, Nat.reduceMod, Nat.reducePow, Nat.reduceSub] at h0 h2
    rw [h134] at h0; cases h0
    rw [h130] at h2; cases h2
    cases b3
    swap; · exact absurd h3 (by simp [Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.AluOp.flagsN,
      Silmaril.X86.Ext.subFlagsN, Silmaril.X86.Ext.isZeroN, hL])
    refine k _ ?_ ?_ ?_ (state_fs _ _)
    · blk_simp [blk5f99, hrip, ripadd, Nat.reduceAdd]
    · blk_simp [blk5f99]; rw [qi_m8]
      simp [Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.AluOp.flagsN, Silmaril.X86.Ext.logicFlagsN,
        Silmaril.X86.Ext.isZeroN]
    · intro r h1 h2; exact state_read_other (by simp [h1, h2])
  · simp only [h130]; exact ⟨_, rfl⟩
  · simp only [h134]; exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- `0x5faa`: `je 0x6220`. -/
theorem qx5faa (hd : c.g.done = none) (hC : QC W b c.m.memory 0x5f99 quoteX4Text)
    (hrip : c.m.core.rip = b + 0x5faa#64) (hf : Silmaril.X86.Ext.Cond.eval c.m.core.flags .e = some true)
    (k : ∀ c1 : State, c1.rip = b + 0x6220#64 → (∀ r, c1.read r = c.m.core.read r) →
      c1.fsBase = c.m.core.fsBase → MustQ W Q ⟨⟨c1, c.m.memory⟩, c.g⟩) : MustQ W Q c := by
  refine must_blkX_at blk5faa blk5faa_ok hd hC.img hC.ld hC.ro (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp [blk5faa]
  · rename_i b0 h0
    have e0 : b0 = true := qi_bool h0 hf
    subst e0
    refine k _ ?_ (fun r => state_read_other (by simp)) (state_fs _ _)
    blk_simp [blk5faa, hrip, ripadd, Nat.reduceAdd, sel1]
  · exact ⟨_, hf⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- `0x6220`, `0x6229`: `backslash_escapes` is set: no closing quote, to `0x622b`. -/
theorem qx6220 (hd : c.g.done = none) (hC : QC W b c.m.memory 0x6220 quoteX5Text)
    (hrip : c.m.core.rip = b + 0x6220#64) (hbp : c.m.core.read .rbp = R - 0xd8#64)
    (h135 : loadN c.m.memory (R - 0x135#64) 1 = some 1#64)
    (k : ∀ c1 : State, c1.rip = b + 0x6229#64 → Silmaril.X86.Ext.Cond.eval c1.flags .ne = some false →
      c1.read .rax = 0#64 → (∀ r, r ≠ .rax → r ≠ .rdx → c1.read r = c.m.core.read r) →
      c1.fsBase = c.m.core.fsBase → MustQ W Q ⟨⟨c1, c.m.memory⟩, c.g⟩) : MustQ W Q c := by
  refine must_blkX_at blk6220 blk6220_ok hd hC.img hC.ld hC.ro (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp [blk6220, hbp, bsub_add, Nat.reduceAdd, Nat.reduceMod, Nat.reducePow, Nat.reduceSub]
  · rename_i v0 h0
    simp only [hbp, bsub_add, Nat.reduceAdd, Nat.reduceMod, Nat.reducePow, Nat.reduceSub] at h0
    rw [h135] at h0; cases h0
    refine k _ ?_ ?_ ?_ ?_ (state_fs _ _)
    · blk_simp [blk6220, hrip, ripadd, Nat.reduceAdd]
    · blk_simp [blk6220]
      simp [Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.AluOp.flagsN, Silmaril.X86.Ext.logicFlagsN,
        Silmaril.X86.Ext.kNot, Silmaril.X86.Ext.isZeroN]
    · blk_simp [blk6220]; decide
    · intro r h1 h2; exact state_read_other (by simp [h1, h2])
  · simp only [h135]; exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- `0x6229`: `jne` not taken. -/
theorem qx6229 (hd : c.g.done = none) (hC : QC W b c.m.memory 0x6220 quoteX5Text)
    (hrip : c.m.core.rip = b + 0x6229#64) (hf : Silmaril.X86.Ext.Cond.eval c.m.core.flags .ne = some false)
    (k : ∀ c1 : State, c1.rip = b + 0x622b#64 → (∀ r, c1.read r = c.m.core.read r) →
      c1.fsBase = c.m.core.fsBase → MustQ W Q ⟨⟨c1, c.m.memory⟩, c.g⟩) : MustQ W Q c := by
  refine must_blkX_at blk6229 blk6229_ok hd hC.img hC.ld hC.ro (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp [blk6229]
  · rename_i b0 h0
    have e0 : b0 = false := qi_bool h0 hf
    subst e0
    refine k _ ?_ (fun r => state_read_other (by simp)) (state_fs _ _)
    blk_simp [blk6229, hrip, ripadd, Nat.reduceAdd, sel0]
  · exact ⟨_, hf⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- `0x622b`: `len`, `quote_string` (not `NULL`): to `0x6241`. -/
theorem qx622b (hd : c.g.done = none) (hC : QC W b c.m.memory 0x6220 quoteX5Text)
    (hrip : c.m.core.rip = b + 0x622b#64) (hbp : c.m.core.read .rbp = R - 0xd8#64) {L : Word}
    (h130 : loadN c.m.memory (R - 0x130#64) 8 = some L)
    (h190 : loadN c.m.memory (R - 0x190#64) 8 = some (b + 0x70d7#64)) (hq : b + 0x70d7#64 ≠ 0#64)
    (k : ∀ c1 : State, c1.rip = b + 0x6241#64 → c1.read .rdi = c.m.core.read .r11 →
      c1.read .r10 = c.m.core.read .r9 → c1.read .r11 = L →
      (∀ r, r ≠ .rbx → r ≠ .rdi → r ≠ .r10 → r ≠ .r11 → c1.read r = c.m.core.read r) →
      c1.fsBase = c.m.core.fsBase → MustQ W Q ⟨⟨c1, c.m.memory⟩, c.g⟩) : MustQ W Q c := by
  refine must_blkX_at blk622b blk622b_ok hd hC.img hC.ld hC.ro (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp [blk622b, hbp, bsub_add, Nat.reduceAdd, Nat.reduceMod, Nat.reducePow, Nat.reduceSub]
  all_goals try qx_side
  · rename_i v0 h0 v1 h1 b2 h2
    simp only [hbp, bsub_add, Nat.reduceAdd, Nat.reduceMod, Nat.reducePow, Nat.reduceSub] at h0 h1
    rw [h130] at h0; cases h0
    rw [h190] at h1; cases h1
    cases b2
    swap; · exact absurd h2 (by simp [Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.logicFlagsN, Silmaril.X86.Ext.isZeroN, hq])
    refine k _ ?_ ?_ ?_ ?_ ?_ (state_fs _ _)
    · blk_simp [blk622b, hrip, ripadd, Nat.reduceAdd, sel0]
    · blk_simp [blk622b]
    · blk_simp [blk622b]
    · blk_simp [blk622b]
    · intro r h1 h2 h3 h4; exact state_read_other (by simp [h1, h2, h3, h4])
  · simp only [h190]; exact ⟨_, rfl⟩
  · simp only [h130]; exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- `0x6241`: `rax = 0`: to `0x6270`. -/
theorem qx6241 (hd : c.g.done = none) (hC : QC W b c.m.memory 0x6220 quoteX5Text)
    (hrip : c.m.core.rip = b + 0x6241#64) (hax : c.m.core.read .rax = 0#64)
    (k : ∀ c1 : State, c1.rip = b + 0x6270#64 → (∀ r, c1.read r = c.m.core.read r) →
      c1.fsBase = c.m.core.fsBase → MustQ W Q ⟨⟨c1, c.m.memory⟩, c.g⟩) : MustQ W Q c := by
  refine must_blkX_at blk6241 blk6241_ok hd hC.img hC.ld hC.ro (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp [blk6241]
  all_goals try qx_side
  rename_i b0 h0
  have e0 : b0 = true := qi_bool h0 (by rw [hax]; decide)
  subst e0
  refine k _ ?_ (fun r => state_read_other (by simp)) (state_fs _ _)
  blk_simp [blk6241, hrip, ripadd, Nat.reduceAdd, sel1]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- `0x6270`: `len < 256`: to `0x6614`. -/
theorem qx6270 (hd : c.g.done = none) (hC : QC W b c.m.memory 0x6220 quoteX5Text)
    (hrip : c.m.core.rip = b + 0x6270#64) (hlt : (c.m.core.read .r11).toNat < (c.m.core.read .rdi).toNat)
    (k : ∀ c1 : State, c1.rip = b + 0x6614#64 → (∀ r, c1.read r = c.m.core.read r) →
      c1.fsBase = c.m.core.fsBase → MustQ W Q ⟨⟨c1, c.m.memory⟩, c.g⟩) : MustQ W Q c := by
  refine must_blkX_at blk6270 blk6270_ok hd hC.img hC.ld hC.ro (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp [blk6270]
  all_goals try qx_side
  rename_i b0 h0
  have e0 : b0 = true := by
    simp only [Silmaril.X86.Ext.AluOp.flagsN, BitVec.setWidth_eq] at h0
    rw [eval_b_sub] at h0
    have : (c.m.core.read .r11).ult (c.m.core.read .rdi) = true := by
      simp only [BitVec.ult, decide_eq_true_eq]; exact hlt
    rw [this] at h0; exact (Option.some.inj h0).symm
  subst e0
  refine k _ ?_ (fun r => state_read_other (by simp)) (state_fs _ _)
  blk_simp [blk6270, hrip, ripadd, Nat.reduceAdd, sel1]

end Silmaril.Elf.Link.Dyn.Sha256sum
