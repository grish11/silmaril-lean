module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.QuoteCells

/-! # GNU `sha256sum`: `quotef` from `0x6720` to the loop head (`Task.quotePro`)
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
open Silmaril.X86.FnContract (AbiEntry)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- `0x6720`–`0x6738`: the prologue of `quotearg_n_options`. -/
theorem qp6720 {W : World} {b R : Word} {Q : PState → Prop} {u : PState}
    (hd : u.g.done = none) (hC : QC W b u.m.memory 0x6614 quoteX6Text) (hrip : u.m.core.rip = b + 0x6720#64)
    (hroom : Room W u.m.memory R 2048) (hsp : u.m.core.read .rsp = R - 0x50#64)
    (k : ∀ c1 : State, c1.rip = b + 0x6738#64 → c1.read .rsp = R - 0xb8#64 → c1.read .rbp = R - 0x58#64 →
      c1.read .r12 = u.m.core.read .rsi → (∀ r, r ≠ .rsp → r ≠ .rbp → r ≠ .r12 → c1.read r = u.m.core.read r) →
      c1.fsBase = u.m.core.fsBase →
      MustQ W Q ⟨⟨c1, storeMem (storeMem (storeMem (storeMem (storeMem (storeMem (storeMem u.m.memory
        (R - 0x58#64) 8 (u.m.core.read .rbp)) (R - 0x60#64) 8 (u.m.core.read .r15)) (R - 0x68#64) 8 (u.m.core.read .r14))
        (R - 0x70#64) 8 (u.m.core.read .r13)) (R - 0x78#64) 8 (u.m.core.read .r12)) (R - 0x80#64) 8 (u.m.core.read .rbx))
        (R - 0x90#64) 8 (u.m.core.read .rdi)⟩, u.g⟩) :
    MustQ W Q u := by
  refine must_blkX_at blk6720 blk6720_ok hd hC.img hC.ld hC.ro (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp [blk6720, hsp, bsub_sub, bsub_add, Nat.reduceAdd, hrip]
  · refine k _ ?_ ?_ ?_ ?_ ?_ rfl
    · blk_simp [blk6720, hrip, Nat.reduceAdd]
    · blk_simp [blk6720, hsp, bsub_sub, Nat.reduceAdd]
    · blk_simp [blk6720, hsp, bsub_sub, Nat.reduceAdd]
    · blk_simp [blk6720]
    · intro r h1 h2 h3; exact state_read_other (by simp [h1, h2, h3])
  all_goals exact room_permR hroom (Or.inr rfl) (by omega) (by omega)


theorem sel0 {α : Type} (x y : α) : (if (0#64 : Word) ≠ 0 then x else y) = y := by simp
theorem sel1 {α : Type} (x y : α) : (if (1#64 : Word) ≠ 0 then x else y) = x := by simp

/-- What `__errno_location` returns, from its entry state `c`. -/
def ErrnoPost (E : Env) (W : World) (c t : PState) : Prop :=
  LibRet E W (fun _ => False) c t ∧ t.g = c.g ∧ OthersKept E c t [] ∧
    t.m.core.read .rax = E.errnoA ∧ (∀ e, ErrnoIs E c.m.memory e → ErrnoIs E t.m.memory e) ∧
    Keeps (ErrnoR E) c.m.memory t.m.memory ∧ ErrnoCell E W t.m.memory

theorem errno_ret_eq (b : Word) : b + BitVec.ofNat 64 0x6614 + BitVec.ofNat 64 (292 + 5) = b + 0x673d#64 := by
  rw [ripadd]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `call __errno_location` (`0x6738`). -/
theorem qpErrno {E : Env} {W : World} {b lb R : Word} {Q : PState → Prop} {v : PState}
    (hd : v.g.done = none) (I : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64) (hlz : W.lazy = none)
    (hro : ShaRO b lb v.m.memory)
    (himp : ImpOk W (lb + 0x2a6e0#64) (nm "__errno_location") (errnoLocStep E W))
    (hrip : v.m.core.rip = b + 0x6738#64) (hroom : Room W v.m.memory R 2048)
    (hsp : v.m.core.read .rsp = R - 0xb8#64) (hal : R.toNat % 16 = 8)
    (k : ∀ t, ErrnoPost E W (callEntry v (lb + 0x2a6e0#64) (b + 0x673d#64)) t → MustQ W Q t) : MustQ W Q v := by
  have h4 := hroom.1
  have hC : QC W b v.m.memory 0x6614 quoteX6Text :=
    hro.qc I hb (by omega) (by have : quoteX6Text.length = 326 := (by decide); omega) (by decide) quoteX6_plain
  have hpush : pushMem v.m.memory (v.m.core.read .rsp) (b + BitVec.ofNat 64 0x6614 + BitVec.ofNat 64 (292 + 5)) =
      storeMem v.m.memory (R - BitVec.ofNat 64 0xc0) 8 (b + 0x673d#64) := by
    rw [pushMem_eq, hsp, bsub_sub, errno_ret_eq]
  have hro2 : ShaRO b lb (storeMem v.m.memory (R - BitVec.ofNat 64 0xc0) 8 (b + 0x673d#64)) :=
    hro.storeR I hroom (by omega) (by omega)
  have hlen := shaC_lens.1
  have hpl : Loaded (pushMem v.m.memory (v.m.core.read .rsp) (b + BitVec.ofNat 64 0x6614 + BitVec.ofNat 64 (292 + 5)))
      (b + 0x23c0#64) pltSecText := by
    rw [hpush]
    exact hro2.loaded hb (v := 0x23c0) (by omega) (by omega) (by omega) shaC_plain.1
  have hga : b + 0x23c0#64 + BitVec.ofNat 64 (0x20 + 4 + 6) + BitVec.signExtend 64 0x79fe#32 = b + 0x9de8#64 := by
    simp only [BitVec.add_assoc]; rfl
  have hslot : loadN (pushMem v.m.memory (v.m.core.read .rsp) (b + BitVec.ofNat 64 0x6614 + BitVec.ofNat 64 (292 + 5)))
      (b + 0x23c0#64 + BitVec.ofNat 64 (0x20 + 4 + 6) + BitVec.signExtend 64 0x79fe#32) 8 = some (lb + 0x2a6e0#64) := by
    rw [hpush, hga]; exact (hro2.got hb).1
  refine must_plt_call (base := b + BitVec.ofNat 64 0x6614) (code := quoteX6Text)
    (L := [(292, .ext8 (.base (.call 0xffffbca3#32)), 5)]) (o := 292) (pb := b + 0x23c0#64) (so := 0x20)
    (f := .named (nm "__errno_location")) hd hlz (by decide +kernel) rfl
    (by rw [hrip]; exact sha_in' I hb (by decide)) hC.ld (by rw [hrip, ripadd]) shaC_listing_ok.1 rfl rfl
    (by simp only [BitVec.add_assoc]; rfl) (img_off I hb (by decide)) (img_off I hb (by decide))
    (by rw [hsp, bsub_sub]; exact room_permR hroom (Or.inr rfl) (by omega) (by omega))
    hpl hslot
    himp.1 himp.2.1 himp.2.2.1 (fun r h => (impOk_fn himp _ r).1 h) ?_
    (fun t ht => k t (by rw [errno_ret_eq] at ht; exact ht))

  have hpr : (pushMem v.m.memory (v.m.core.read .rsp) (b + BitVec.ofNat 64 0x6614 + BitVec.ofNat 64 (292 + 5))).readBytes
      (v.m.core.read .rsp - 8#64).toNat 8 = some (Silmaril.Machine.LittleEndian.encodeWords
        [b + BitVec.ofNat 64 0x6614 + BitVec.ofNat 64 (292 + 5)]) :=
    pushMem_read (by rw [hsp, bsub_sub]; exact room_permR hroom (Or.inl rfl) (by omega) (by omega))
      (by rw [hsp, bsub_sub]; exact room_permR hroom (Or.inr rfl) (by omega) (by omega))
  refine Silmaril.Elf.Link.Dyn.Hello.abiEntry_of ?_ (by simpa using hpr)
  simp only [callEntry_rsp, hsp, bsub_sub, Nat.reduceAdd]
  rw [bsub_toNat (by omega)]
  omega


set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- `0x673d`–`0x6754`: `errno` saved at `R - 0x94`, `nslots = 1 > 0`: to `0x681c`. -/
theorem qp673d {W : World} {b R : Word} {Q : PState → Prop} {v : PState} {ea ev : Word}
    (hd : v.g.done = none) (hC : QC W b v.m.memory 0x6614 quoteX6Text) (hrip : v.m.core.rip = b + 0x673d#64)
    (hroom : Room W v.m.memory R 2048) (hbp : v.m.core.read .rbp = R - 0x58#64) (hax : v.m.core.read .rax = ea)
    (hsl : QSlots b v.m.memory) (hev : loadN v.m.memory ea 4 = some ev)
    (k : ∀ c1 : State, c1.rip = b + 0x681c#64 → c1.read .rbx = ea → c1.read .r15 = b + 0xa020#64 →
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rbx → r ≠ .r15 → c1.read r = v.m.core.read r) →
      c1.fsBase = v.m.core.fsBase →
      MustQ W Q ⟨⟨c1, storeMem v.m.memory (R - 0x94#64) 4 ev⟩, v.g⟩) :
    MustQ W Q v := by
  have hn : v.m.core.rip + 0x38d3#64 = b + 0xa010#64 := by rw [hrip]; bv_omega
  have hv : v.m.core.rip + 0x38f3#64 = b + 0xa030#64 := by rw [hrip]; bv_omega
  have hz : (ev.setWidth 32).setWidth 64 = ev := zext_small (loadN_lt hev) (by omega)
  refine must_blkX_at blk673d blk673d_ok hd hC.img hC.ld hC.ro (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp [blk673d, hbp, hax, bsub_add, Nat.reduceAdd, Nat.reduceMod, Nat.reducePow,
    Nat.reduceSub, hn, hv, hsl.nslots, hsl.vec, hev]
  · rename_i v0 h0 v1 h1 v2 h2 bv hbv
    rw [hn, hsl.nslots] at h0; cases h0
    rw [hv, hsl.vec] at h1; cases h1
    rw [hax, hev] at h2; cases h2
    cases bv
    · exact absurd hbv (by decide)
    simp only [hz]
    refine k _ ?_ ?_ ?_ ?_ rfl
    · blk_simp [blk673d, hrip, Nat.reduceAdd]; rfl
    · blk_simp [blk673d, hax]
    · blk_simp [blk673d]
    · intro r h1 h2 h3 h4; exact state_read_other (by simp [h1, h2, h3, h4])
  all_goals first
    | exact ⟨_, rfl⟩
    | exact eval_some (defined_logic _) _
    | exact room_permR hroom (Or.inr rfl) (by omega) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `0x681c`–`0x6854`: the arguments of `quotearg_buffer_restyled`. -/
theorem qp681c {W : World} {b R : Word} {Q : PState → Prop} {c : PState} {nm : Word}
    (hd : c.g.done = none) (hC : QC W b c.m.memory 0x681c quoteX7Text) (hrip : c.m.core.rip = b + 0x681c#64)
    (hroom : Room W c.m.memory R 2048) (hbp : c.m.core.read .rbp = R - 0x58#64)
    (hsp : c.m.core.read .rsp = R - 0xb8#64) (hr12 : c.m.core.read .r12 = R - 0x48#64)
    (hr15 : c.m.core.read .r15 = b + 0xa020#64) (hsl : QSlots b c.m.memory)
    (h44 : loadN c.m.memory (R - 0x44#64) 4 = some 0#64) (h48 : loadN c.m.memory (R - 0x48#64) 4 = some 3#64)
    (h90 : loadN c.m.memory (R - 0x90#64) 8 = some nm) (h18 : loadN c.m.memory (R - 0x18#64) 8 = some 0#64)
    (h20 : loadN c.m.memory (R - 0x20#64) 8 = some 0#64)
    (k : ∀ c1 : State, c1.rip = b + 0x6854#64 → c1.read .rsp = R - 0xc8#64 → c1.read .rdi = b + 0xa060#64 →
      c1.read .rsi = 256#64 → c1.read .rdx = nm → c1.read .rcx = 3#64 → c1.read .r8 = 1#64 →
      c1.read .r9 = R - 0x40#64 → c1.read .r13 = b + 0xa060#64 → c1.read .r14 = 256#64 →
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsp → r ≠ .rsi → r ≠ .rdi → r ≠ .r8 → r ≠ .r9 →
        r ≠ .r13 → r ≠ .r14 → c1.read r = c.m.core.read r) →
      c1.fsBase = c.m.core.fsBase →
      MustQ W Q ⟨⟨c1, storeMem (storeMem (storeMem (storeMem c.m.memory (R - 0xa8#64) 8 (R - 0x40#64))
        (R - 0xa0#64) 4 1#64) (R - 0xc0#64) 8 0#64) (R - 0xc8#64) 8 0#64⟩, c.g⟩) :
    MustQ W Q c := by
  have h4 := hroom.1
  refine must_blkX_at blk681c blk681c_ok hd hC.img hC.ld hC.ro (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp [blk681c, hbp, hsp, hr12, hr15, bsub_add, bsub_sub, Nat.reduceAdd, Nat.reduceMod,
    Nat.reducePow, Nat.reduceSub, BitVec.add_zero]
  all_goals try simp (disch := omega) only [loadN_stR] at *
  · rename_i v0 h0 v1 h1 v2 h2 v3 h3 v4 h4' v5 h5 v6 h6
    simp only [hbp, hsp, hr12, hr15, bsub_add, bsub_sub, ripadd, Nat.reduceAdd, Nat.reduceMod, Nat.reducePow,
      Nat.reduceSub] at h0 h1 h2 h3 h4' h5 h6
    rw [h44] at h0; cases h0
    rw [hsl.size] at h1; cases h1
    rw [hsl.val] at h2; cases h2
    rw [h48] at h3; cases h3
    simp (disch := omega) only [loadN_stR] at h4' h5 h6
    rw [h90] at h4'; cases h4'
    rw [h18] at h5; cases h5
    rw [h20] at h6; cases h6
    simp only [BitVec.reduceSetWidth, BitVec.reduceOr]
    refine k _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    pick_goal 11
    · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
      exact state_read_other (by simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10])
    all_goals (blk_simp [blk681c, hrip, hbp, hsp, hr12, hr15, bsub_add, bsub_sub, ripadd, Nat.reduceAdd,
      Nat.reduceMod, Nat.reducePow, Nat.reduceSub, BitVec.reduceSetWidth, BitVec.reduceOr])
  all_goals first
    | (simp only [h44, h48, h90, h18, h20, hsl.size, hsl.val]; exact ⟨_, rfl⟩)
    | exact room_permR hroom (Or.inr rfl) (by omega) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- `call quotearg_buffer_restyled` (`0x6854`). -/
theorem qpCall {W : World} {b : Word} {Q : PState → Prop} {c : PState}
    (hd : c.g.done = none) (hC : QC W b c.m.memory 0x681c quoteX7Text) (hrip : c.m.core.rip = b + 0x6854#64)
    (hw : c.m.memory.Permitted .write (c.m.core.read .rsp - 8#64).toNat 8)
    (k : ∀ c1 : State, c1.rip = b + 0x4f50#64 → c1.read .rsp = c.m.core.read .rsp - 8#64 →
      (∀ r, r ≠ .rsp → c1.read r = c.m.core.read r) → c1.fsBase = c.m.core.fsBase →
      MustQ W Q ⟨⟨c1, pushMem c.m.memory (c.m.core.read .rsp) (b + 0x6859#64)⟩, c.g⟩) :
    MustQ W Q c := by
  refine must_insn (base := b + BitVec.ofNat 64 0x681c) (o := 56) (l := 5)
    (i := .ext8 (.base (.call 0xffffe6f7#32))) hd (by rw [hrip]; exact hC.img 56 (by decide)) hC.ld
    (by rw [hrip, ripadd]) (by decide) (by decide +kernel) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem hw]
  simp only [WP_ok]
  rw [show c.m.core.rip + 5#64 = b + 0x6859#64 by rw [hrip]; bv_omega]
  refine k _ ?_ ?_ ?_ rfl
  · simp
  · simp
  · intro r hr; simp [hr]

/-- Stores into the stack page keep `OutStk`. -/
syntax "keeps_out" : tactic
macro_rules
  | `(tactic| keeps_out) => `(tactic|
      ((repeat (refine keeps_storeMem_right ?_ ?_; pick_goal 2))
       (try exact Keeps.refl _ _)
       all_goals (intro x hx; unfold OutStk at hx; rw [bsub_toNat (by omega)]; omega)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- `0x4f50`–`0x4fa8`: the prologue of `quotearg_buffer_restyled`. -/
theorem qp4f50 {W : World} {b R : Word} {Q : PState → Prop} {c : PState} {nm ea g : Word}
    (hd : c.g.done = none) (hC : QC W b c.m.memory 0x4f50 quoteX0Text) (hrip : c.m.core.rip = b + 0x4f50#64)
    (hroom : Room W c.m.memory R 2048) (hsp : c.m.core.read .rsp = R - 0xd0#64)
    (hbp : c.m.core.read .rbp = R - 0x58#64) (hr15 : c.m.core.read .r15 = b + 0xa020#64)
    (hr14 : c.m.core.read .r14 = 256#64) (hr13 : c.m.core.read .r13 = b + 0xa060#64)
    (hr12 : c.m.core.read .r12 = R - 0x48#64) (hbx : c.m.core.read .rbx = ea)
    (hdi : c.m.core.read .rdi = b + 0xa060#64) (hsi : c.m.core.read .rsi = 256#64) (hdx : c.m.core.read .rdx = nm)
    (hcx : c.m.core.read .rcx = 3#64) (hr8 : c.m.core.read .r8 = 1#64) (hr9 : c.m.core.read .r9 = R - 0x40#64)
    (hc8 : loadN c.m.memory (R - 0xc8#64) 8 = some 0#64) (hc0 : loadN c.m.memory (R - 0xc0#64) 8 = some 0#64)
    (hgs : ∀ m', Keeps (OutStk R) c.m.memory m' → loadN m' (c.m.core.fsBase + 0x28#64) 8 = some g)
    (k : ∀ c1 : State, c1.rip = b + 0x4fa8#64 → c1.read .rsp = R - 0x1c8#64 → c1.read .rbp = R - 0xd8#64 →
      c1.read .r9 = b + 0xa060#64 → c1.read .r11 = 256#64 → c1.read .r14 = 0xffffffffffffffff#64 →
      c1.fsBase = c.m.core.fsBase →
      MustQ W Q ⟨⟨c1, storeMem (storeMem (storeMem (storeMem (storeMem (storeMem (storeMem (storeMem (storeMem
        (storeMem (storeMem (storeMem (storeMem c.m.memory
        (R - 0xd8#64) 8 (R - 0x58#64)) (R - 0xe0#64) 8 (b + 0xa020#64)) (R - 0xe8#64) 8 256#64)
        (R - 0xf0#64) 8 (b + 0xa060#64)) (R - 0xf8#64) 8 (R - 0x48#64)) (R - 0x100#64) 8 ea)
        (R - 0x158#64) 8 (R - 0x40#64)) (R - 0x148#64) 8 nm) (R - 0x194#64) 4 1#64)
        (R - 0x110#64) 8 g) (R - 0x134#64) 4 3#64) (R - 0x140#64) 8 256#64) (R - 0x130#64) 8 (b + 0xa060#64)⟩,
        c.g⟩) :
    MustQ W Q c := by
  have h4 := hroom.1
  refine must_blkX_at blk4f50 blk4f50_ok hd hC.img hC.ld hC.ro (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp [blk4f50, hbp, hsp, hr12, hr13, hr14, hr15, hbx, hdi, hsi, hdx, hcx, hr8, hr9, bsub_add,
    bsub_sub, Nat.reduceAdd, Nat.reduceMod, Nat.reducePow, Nat.reduceSub, BitVec.reduceSetWidth]
  all_goals try simp (disch := omega) only [loadN_stR] at *
  · rename_i v0 h0 v1 h1 v2 h2
    simp only [hbp, hsp, hr12, hr13, hr14, hr15, hbx, hdi, hsi, hdx, hcx, hr8, hr9, bsub_add, bsub_sub,
      Nat.reduceAdd, Nat.reduceMod, Nat.reducePow, Nat.reduceSub, BitVec.reduceSetWidth] at h0 h1 h2
    simp (disch := omega) only [loadN_stR] at h0 h1
    rw [hc8] at h0; cases h0
    rw [hc0] at h1; cases h1
    rw [hgs _ (by keeps_out)] at h2; cases h2
    refine k _ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    all_goals (blk_simp [blk4f50, hrip, hbp, hsp, hdi, hsi, bsub_add, bsub_sub, ripadd, Nat.reduceAdd,
      Nat.reduceMod, Nat.reducePow, Nat.reduceSub, BitVec.reduceSetWidth])
  all_goals first
    | (simp only [hc8, hc0]; exact ⟨_, rfl⟩)
    | exact ⟨_, hgs _ (by keeps_out)⟩
    | exact room_permR hroom (Or.inr rfl) (by omega) (by omega)

/-- What `__ctype_get_mb_cur_max` returns, from its entry state `c`. -/
def MbPost (E : Env) (W : World) (c t : PState) : Prop :=
  LibRet E W (fun _ => False) c t ∧ t.g = c.g ∧ OthersKept E c t [] ∧ t.m.core.read .rax = 1#64 ∧
    Keeps (ErrnoR E) c.m.memory t.m.memory

theorem mb_ret_eq (b : Word) : b + BitVec.ofNat 64 0x4f50 + BitVec.ofNat 64 (88 + 5) = b + 0x4fad#64 := by
  rw [ripadd]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `call __ctype_get_mb_cur_max` (`0x4fa8`). -/
theorem qpMb {E : Env} {W : World} {b lb R : Word} {Q : PState → Prop} {v : PState}
    (hd : v.g.done = none) (I : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64) (hlz : W.lazy = none)
    (hro : ShaRO b lb v.m.memory)
    (himp : ImpOk W (lb + 0x39480#64) (nm "__ctype_get_mb_cur_max") (mbCurMaxStep E W))
    (hrip : v.m.core.rip = b + 0x4fa8#64) (hroom : Room W v.m.memory R 2048)
    (hsp : v.m.core.read .rsp = R - 0x1c8#64) (hal : R.toNat % 16 = 8)
    (k : ∀ t, MbPost E W (callEntry v (lb + 0x39480#64) (b + 0x4fad#64)) t → MustQ W Q t) : MustQ W Q v := by
  have h4 := hroom.1
  have hC : QC W b v.m.memory 0x4f50 quoteX0Text :=
    hro.qc I hb (by omega) (by have : quoteX0Text.length = 496 := (by decide); omega) (by decide) quoteX0_plain
  have hpush : pushMem v.m.memory (v.m.core.read .rsp) (b + BitVec.ofNat 64 0x4f50 + BitVec.ofNat 64 (88 + 5)) =
      storeMem v.m.memory (R - BitVec.ofNat 64 0x1d0) 8 (b + 0x4fad#64) := by
    rw [pushMem_eq, hsp, bsub_sub, mb_ret_eq]
  have hro2 : ShaRO b lb (storeMem v.m.memory (R - BitVec.ofNat 64 0x1d0) 8 (b + 0x4fad#64)) :=
    hro.storeR I hroom (by omega) (by omega)
  have hlen := shaC_lens.1
  have hpl : Loaded (pushMem v.m.memory (v.m.core.read .rsp) (b + BitVec.ofNat 64 0x4f50 + BitVec.ofNat 64 (88 + 5)))
      (b + 0x23c0#64) pltSecText := by
    rw [hpush]
    exact hro2.loaded hb (v := 0x23c0) (by omega) (by omega) (by omega) shaC_plain.1
  have hga : b + 0x23c0#64 + BitVec.ofNat 64 (0x40 + 4 + 6) + BitVec.signExtend 64 0x79ee#32 = b + 0x9df8#64 := by
    simp only [BitVec.add_assoc]; rfl
  have hslot : loadN (pushMem v.m.memory (v.m.core.read .rsp) (b + BitVec.ofNat 64 0x4f50 + BitVec.ofNat 64 (88 + 5)))
      (b + 0x23c0#64 + BitVec.ofNat 64 (0x40 + 4 + 6) + BitVec.signExtend 64 0x79ee#32) 8 = some (lb + 0x39480#64) := by
    rw [hpush, hga]; exact (hro2.got hb).2
  refine must_plt_call (base := b + BitVec.ofNat 64 0x4f50) (code := quoteX0Text)
    (L := [(88, .ext8 (.base (.call 0xffffd453#32)), 5)]) (o := 88) (pb := b + 0x23c0#64) (so := 0x40)
    (f := .named (nm "__ctype_get_mb_cur_max")) hd hlz (by decide +kernel) rfl
    (by rw [hrip]; exact sha_in' I hb (by decide)) hC.ld (by rw [hrip, ripadd]) shaC_listing_ok.1 rfl rfl
    (by simp only [BitVec.add_assoc]; rfl) (img_off I hb (by decide)) (img_off I hb (by decide))
    (by rw [hsp, bsub_sub]; exact room_permR hroom (Or.inr rfl) (by omega) (by omega))
    hpl hslot
    himp.1 himp.2.1 himp.2.2.1 (fun r h => (impOk_fn himp _ r).1 h) ?_
    (fun t ht => k t (by rw [mb_ret_eq] at ht; exact ht))
  have hpr : (pushMem v.m.memory (v.m.core.read .rsp) (b + BitVec.ofNat 64 0x4f50 + BitVec.ofNat 64 (88 + 5))).readBytes
      (v.m.core.read .rsp - 8#64).toNat 8 = some (Silmaril.Machine.LittleEndian.encodeWords
        [b + BitVec.ofNat 64 0x4f50 + BitVec.ofNat 64 (88 + 5)]) :=
    pushMem_read (by rw [hsp, bsub_sub]; exact room_permR hroom (Or.inl rfl) (by omega) (by omega))
      (by rw [hsp, bsub_sub]; exact room_permR hroom (Or.inr rfl) (by omega) (by omega))
  refine Silmaril.Elf.Link.Dyn.Hello.abiEntry_of ?_ (by simpa using hpr)
  simp only [callEntry_rsp, hsp, bsub_sub, Nat.reduceAdd]
  rw [bsub_toNat (by omega)]
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `0x4fad`–`0x4fcd`: `MB_CUR_MAX` saved, `backslash_escapes = false`, style `3 ≤ 10`. -/
theorem qp4fad {W : World} {b R : Word} {Q : PState → Prop} {c : PState}
    (hd : c.g.done = none) (hC : QC W b c.m.memory 0x4f50 quoteX0Text) (hrip : c.m.core.rip = b + 0x4fad#64)
    (hroom : Room W c.m.memory R 2048) (hbp : c.m.core.read .rbp = R - 0xd8#64) (hax : c.m.core.read .rax = 1#64)
    (h194 : loadN c.m.memory (R - 0x194#64) 4 = some 1#64) (h134 : loadN c.m.memory (R - 0x134#64) 4 = some 3#64)
    (k : ∀ c1 : State, c1.rip = b + 0x4fcd#64 → c1.read .rax = 3#64 →
      (∀ r, r ≠ .rax → r ≠ .rbx → c1.read r = c.m.core.read r) → c1.fsBase = c.m.core.fsBase →
      MustQ W Q ⟨⟨c1, storeMem (storeMem c.m.memory (R - 0x1a8#64) 8 1#64) (R - 0x135#64) 1 0#64⟩, c.g⟩) :
    MustQ W Q c := by
  have h4 := hroom.1
  refine must_blkX_at blk4fad blk4fad_ok hd hC.img hC.ld hC.ro (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp [blk4fad, hbp, hax, bsub_add, bsub_sub, Nat.reduceAdd, Nat.reduceMod, Nat.reducePow,
    Nat.reduceSub, BitVec.reduceSetWidth]
  all_goals try simp (disch := omega) only [loadN_stR] at *
  · rename_i v0 h0 v1 h1 bv2 hb2 bv3 hb3
    simp only [hbp, bsub_add, bsub_sub, Nat.reduceAdd, Nat.reduceMod, Nat.reducePow, Nat.reduceSub] at h0 h1
    simp (disch := omega) only [loadN_stR] at h1
    rw [h194] at h0; cases h0
    rw [h134] at h1; cases h1
    cases bv2
    swap; · exact absurd hb2 (by decide)
    cases bv3
    swap; · exact absurd hb3 (by decide)
    simp only [Bool.false_eq_true, ↓reduceIte, BitVec.reduceSetWidth]
    refine k _ ?_ ?_ ?_ rfl
    pick_goal 3
    · intro r h1 h2; exact state_read_other (by simp [h1, h2])
    all_goals (blk_simp [blk4fad, hrip, ripadd, Nat.reduceAdd, BitVec.reduceSetWidth, Bool.false_eq_true,
      ↓reduceIte, sel0])
  all_goals first
    | (simp only [h194, h134]; exact ⟨_, rfl⟩)
    | exact eval_some (defined_alu _ _ _ _) _
    | exact room_permR hroom (Or.inr rfl) (by omega) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `0x4fcd`–`0x4fe6`: the style jump table (`0x7f48`, entry 3): to `0x588a`. -/
theorem qp4fcd {W : World} {b R : Word} {Q : PState → Prop} {c : PState}
    (hd : c.g.done = none) (hC : QC W b c.m.memory 0x4f50 quoteX0Text) (hrip : c.m.core.rip = b + 0x4fcd#64)
    (hroom : Room W c.m.memory R 2048) (hbp : c.m.core.read .rbp = R - 0xd8#64) (hax : c.m.core.read .rax = 3#64)
    (h130 : loadN c.m.memory (R - 0x130#64) 8 = some (b + 0xa060#64))
    (h140 : loadN c.m.memory (R - 0x140#64) 8 = some 256#64)
    (hjt : loadN c.m.memory (b + 0x7f54#64) 4 = some 0xffffd942#64)
    (k : ∀ c1 : State, c1.rip = b + 0x588a#64 → c1.read .r9 = b + 0xa060#64 → c1.read .r11 = 256#64 →
      (∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .r9 → r ≠ .r11 → c1.read r = c.m.core.read r) →
      c1.fsBase = c.m.core.fsBase → MustQ W Q ⟨⟨c1, c.m.memory⟩, c.g⟩) :
    MustQ W Q c := by
  have h4 := hroom.1
  have ha : c.m.core.rip + 0x2f7b#64 + (c.m.core.read .rax <<< 2) = b + 0x7f54#64 := by
    rw [hrip, hax]; bv_omega
  refine must_blkX_at blk4fcd blk4fcd_ok hd hC.img hC.ld hC.ro (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp [blk4fcd, hbp, ha, bsub_add, bsub_sub, Nat.reduceAdd, Nat.reduceMod, Nat.reducePow,
    Nat.reduceSub]
  · rename_i v0 h0 v1 h1 v2 h2
    simp only [hbp, ha, bsub_add, bsub_sub, Nat.reduceAdd, Nat.reduceMod, Nat.reducePow, Nat.reduceSub] at h0 h1 h2
    rw [h130] at h0; cases h0
    rw [h140] at h1; cases h1
    rw [hjt] at h2; cases h2
    refine k _ ?_ ?_ ?_ ?_ rfl
    pick_goal 4
    · intro r h1 h2 h3 h4; exact state_read_other (by simp [h1, h2, h3, h4])
    · blk_simp [blk4fcd, hrip, BitVec.reduceSetWidth, BitVec.reduceSignExtend]; bv_omega
    all_goals blk_simp [blk4fcd]
  all_goals first
    | (simp only [h130, h140, hjt]; exact ⟨_, rfl⟩)


end Silmaril.Elf.Link.Dyn.Sha256sum
