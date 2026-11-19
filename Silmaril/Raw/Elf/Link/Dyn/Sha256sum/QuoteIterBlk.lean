module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.QuoteIterByte

/-! # GNU `sha256sum`: the blocks of one iteration of `quotearg_buffer_restyled`'s loop

One lemma per block (`CertQuoteX` certificates, `must_blkX_at`), for a safe byte `c` with
`shell_always_quoting_style` (style `2`, quote string `'`, `backslash_escapes` off, `quote_these_too`
= `:` only): `0x50c0`, `0x50cd`, `0x50d9`, `0x50e2`, `0x50f0`, `0x5102`, `0x510b`, then
`0x5118`, `0x5121`, `0x512b` (byte table, `c ≤ 0x3f`) or `0x5cc0`, `0x5cc6`, `0x5cd0` (`c > 0x3f`),
then `0x5165`, `0x516b`, `0x5171`, `0x5180`, `0x5185`, `0x5248`, `0x5258`, `0x5262`, `0x5207`,
`0x5210` (the byte stored in `slot0`), `0x5214` (back to `0x50c0`). Each states its successor
abstractly (`QiS`: memory, ghost, `fs` and the unlisted registers kept). -/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Cert

/-- The code facts of the loop's chunks (`0x4f50`, `0x5165`, `0x5cc0`) on memory `M`. -/
structure QiCode (W : World) (b : Word) (M : Memory) : Prop where
  img0 : ∀ n, n < quoteX0Text.length → W.InImage (b + BitVec.ofNat 64 (0x4f50 + n)).toNat
  ld0 : Loaded M (b + BitVec.ofNat 64 0x4f50) quoteX0Text
  ro0 : CodeRO M (b + BitVec.ofNat 64 0x4f50) quoteX0Text
  img1 : ∀ n, n < quoteX1Text.length → W.InImage (b + BitVec.ofNat 64 (0x5165 + n)).toNat
  ld1 : Loaded M (b + BitVec.ofNat 64 0x5165) quoteX1Text
  ro1 : CodeRO M (b + BitVec.ofNat 64 0x5165) quoteX1Text
  img3 : ∀ n, n < quoteX3Text.length → W.InImage (b + BitVec.ofNat 64 (0x5cc0 + n)).toNat
  ld3 : Loaded M (b + BitVec.ofNat 64 0x5cc0) quoteX3Text
  ro3 : CodeRO M (b + BitVec.ofNat 64 0x5cc0) quoteX3Text

/-- `v'` keeps `v`'s memory, ghost, `fs` and every register outside `rs`. -/
def QiS (v v' : PState) (rs : List Reg) : Prop :=
  v'.m.memory = v.m.memory ∧ v'.g = v.g ∧ v'.m.core.fsBase = v.m.core.fsBase ∧
    ∀ r, r ∉ rs → v'.m.core.read r = v.m.core.read r

theorem qi_bool {o : Option Bool} {x y : Bool} (h : o = some x) (h' : o = some y) : x = y :=
  Option.some.inj (h.symm.trans h')

theorem qi_load {m : Memory} {a v w : Word} {k : Nat} (h : loadN m a k = some v) (h' : loadN m a k = some w) :
    v = w := Option.some.inj (h.symm.trans h')

macro "qi_side" : tactic => `(tactic| (show ∃ bv : Bool, _; first
  | exact eval_some (defined_alu _ _ _ _) _
  | exact eval_some (defined_logic _) _))

/-- Close a goal that depends on the byte `c` only, by `decide` over the 256 bytes. -/
macro "qi_dec" c:ident : tactic => `(tactic| (generalize $c:ident = x; revert x; apply qi_all; decide +kernel))

theorem qi_z8 (c : Byte) : BitVec.setWidth 64 (BitVec.setWidth 8 (bw c)) = bw c := by
  revert c; apply qi_all; decide +kernel

macro "qi_rip" : tactic => `(tactic| all_goals first | rfl | (simp; done) | bv_omega | (simp; bv_omega))

variable {W : World} {b : Word} {Q : PState → Prop} {v : PState}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem qi_50c0 (hd : v.g.done = none) (hC : QiCode W b v.m.memory) (hrip : v.m.core.rip = b + 0x50c0#64)
    (hr14 : v.m.core.read .r14 = 0xffffffffffffffff#64)
    (k : ∀ v' : PState, QiS v v' [.r10] → v'.m.core.rip = b + 0x50cd#64 → MustQ W Q v') : MustQ W Q v := by
  refine must_blkX_at (cb := 0x4f50) blk50c0 blk50c0_ok hd hC.img0 hC.ld0 hC.ro0 (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp [blk50c0]
  all_goals try qi_side
  rename_i b0 h0 b1 h1
  have e1 : b1 = false := qi_bool h1 (by rw [hr14]; decide)
  refine k _ ⟨rfl, rfl, rfl, fun r hr => state_read_other (by simpa [blk50c0] using hr)⟩ ?_
  blk_simp [blk50c0, hrip, e1]
  qi_rip

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem qi_50cd (hd : v.g.done = none) (hC : QiCode W b v.m.memory) (hrip : v.m.core.rip = b + 0x50cd#64)
    {nm : Word} {c : Byte} (hs : QSafe c)
    (hnm : loadN v.m.memory (v.m.core.read .rbp + 0xffffffffffffff90#64) 8 = some nm)
    (hc : loadN v.m.memory (nm + v.m.core.read .rbx) 1 = some (bw c))
    (k : ∀ v' : PState, QiS v v' [.rax, .r10] → v'.m.core.rip = b + 0x50d9#64 →
      v'.m.core.read .rax = nm → (v'.m.core.read .r10).setWidth 8 = 1#8 → MustQ W Q v') : MustQ W Q v := by
  refine must_blkX_at (cb := 0x4f50) blk50cd blk50cd_ok hd hC.img0 hC.ld0 hC.ro0 (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp [blk50cd]
  all_goals try qi_side
  · rename_i v0 h0 v1 h1 b2 h2
    have e0 := qi_load h0 hnm
    have e1 : v1 = bw c := qi_load h1 (by rw [e0]; exact hc)
    have e2 : b2 = true := qi_bool h2 (by rw [e1]; exact qi_c50cd c hs)
    refine k _ ⟨rfl, rfl, rfl, fun r hr => state_read_other (by simpa [blk50cd] using hr)⟩ ?_ ?_ ?_
    · blk_simp [blk50cd, hrip]
    · blk_simp [blk50cd]; exact e0
    · blk_simp [blk50cd, e2]; rw [qi_m8]; decide
  · rename_i v0 h0; rw [qi_load h0 hnm]; exact ⟨_, hc⟩
  · exact ⟨_, hnm⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem qi_50d9 (hd : v.g.done = none) (hC : QiCode W b v.m.memory) (hrip : v.m.core.rip = b + 0x50d9#64)
    (hr10 : (v.m.core.read .r10).setWidth 8 = 1#8)
    (k : ∀ v' : PState, QiS v v' [] → v'.m.core.rip = b + 0x50e2#64 → MustQ W Q v') : MustQ W Q v := by
  refine must_blkX_at (cb := 0x4f50) blk50d9 blk50d9_ok hd hC.img0 hC.ld0 hC.ro0 (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp [blk50d9]
  all_goals try qi_side
  rename_i b0 h0
  have e0 : b0 = false := qi_bool h0 (by rw [hr10]; decide)
  refine k _ ⟨rfl, rfl, rfl, fun r hr => state_read_other (by simp)⟩ ?_
  blk_simp [blk50d9, hrip, e0]
  qi_rip

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem qi_50e2 (hd : v.g.done = none) (hC : QiCode W b v.m.memory) (hrip : v.m.core.rip = b + 0x50e2#64)
    {nm : Word}
    (h5c : loadN v.m.memory (v.m.core.read .rbp + 0xffffffffffffffa4#64) 4 = some 2#64)
    (hnm : loadN v.m.memory (v.m.core.read .rbp + 0xffffffffffffff90#64) 8 = some nm)
    (h5f : loadN v.m.memory (v.m.core.read .rbp + 0xffffffffffffffa1#64) 1 = some 1#64)
    (k : ∀ v' : PState, QiS v v' [.rax, .rdi] → v'.m.core.rip = b + 0x50f0#64 →
      (v'.m.core.read .rax).setWidth 8 = 0#8 → v'.m.core.read .rdi = nm → MustQ W Q v') : MustQ W Q v := by
  refine must_blkX_at (cb := 0x4f50) blk50e2 blk50e2_ok hd hC.img0 hC.ld0 hC.ro0 (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp [blk50e2]
  · rename_i v0 h0 v1 h1 b2 h2 v3 h3
    have e0 := qi_load h0 h5c
    have e1 := qi_load h1 hnm
    have e3 := qi_load h3 h5f
    have e2 : b2 = false := qi_bool h2 (by rw [e0]; decide)
    refine k _ ⟨rfl, rfl, rfl, fun r hr => state_read_other (by simpa [blk50e2] using hr)⟩ ?_ ?_ ?_
    · blk_simp [blk50e2, hrip]
    · blk_simp [blk50e2, e2, e3]; rw [qi_m8, qi_m8]; decide
    · blk_simp [blk50e2, e1]
  · exact ⟨_, h5f⟩
  · qi_side
  · exact ⟨_, hnm⟩
  · exact ⟨_, h5c⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem qi_50f0 (hd : v.g.done = none) (hC : QiCode W b v.m.memory) (hrip : v.m.core.rip = b + 0x50f0#64)
    (h78 : loadN v.m.memory (v.m.core.read .rbp + 0xffffffffffffff88#64) 8 = some 1#64)
    (hax : (v.m.core.read .rax).setWidth 8 = 0#8)
    (k : ∀ v' : PState, QiS v v' [.rax, .rcx, .r8] → v'.m.core.rip = b + 0x5102#64 →
      (v'.m.core.read .rax).setWidth 8 = 0#8 → v'.m.core.read .rcx = v.m.core.read .rdi + v.m.core.read .rbx →
      (v'.m.core.read .r8).setWidth 8 = 0#8 → Silmaril.X86.Ext.Cond.eval v'.m.core.flags .ne = some false →
      MustQ W Q v') : MustQ W Q v := by
  refine must_blkX_at (cb := 0x4f50) blk50f0 blk50f0_ok hd hC.img0 hC.ld0 hC.ro0 (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp [blk50f0]
  · rename_i v0 h0 b1 h1
    have e0 := qi_load h0 h78
    have e1 : b1 = true := qi_bool h1 (by rw [e0]; decide)
    refine k _ ⟨rfl, rfl, rfl, fun r hr => state_read_other (by simpa [blk50f0] using hr)⟩ ?_ ?_ ?_ ?_ ?_
    · blk_simp [blk50f0, hrip]
    · blk_simp [blk50f0, e1]; rw [qi_m8]; simp [hax]
    · blk_simp [blk50f0]
    · blk_simp [blk50f0]; simp [hax]
    · blk_simp [blk50f0, e1]; simp [hax]; decide
  · qi_side
  · exact ⟨_, h78⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem qi_5102 (hd : v.g.done = none) (hC : QiCode W b v.m.memory) (hrip : v.m.core.rip = b + 0x5102#64)
    (hfl : Silmaril.X86.Ext.Cond.eval v.m.core.flags .ne = some false) (hax : (v.m.core.read .rax).setWidth 8 = 0#8)
    (k : ∀ v' : PState, QiS v v' [.r12] → v'.m.core.rip = b + 0x510b#64 →
      (v'.m.core.read .r12).setWidth 8 = 0#8 → MustQ W Q v') : MustQ W Q v := by
  refine must_blkX_at (cb := 0x4f50) blk5102 blk5102_ok hd hC.img0 hC.ld0 hC.ro0 (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp [blk5102]
  · rename_i b0 h0
    have e0 : b0 = false := qi_bool h0 hfl
    refine k _ ⟨rfl, rfl, rfl, fun r hr => state_read_other (by simpa [blk5102] using hr)⟩ ?_ ?_
    · blk_simp [blk5102, hrip, e0]; qi_rip
    · blk_simp [blk5102]; simp [hax]
  · exact ⟨_, hfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem qi_510b (hd : v.g.done = none) (hC : QiCode W b v.m.memory) (hrip : v.m.core.rip = b + 0x510b#64)
    {c : Byte} (hs : QSafe c) (hc : loadN v.m.memory (v.m.core.read .rcx) 1 = some (bw c))
    (klo : ∀ v' : PState, QiS v v' [.rsi] → c.toNat ≤ 63 → v'.m.core.rip = b + 0x5118#64 →
      v'.m.core.read .rsi = bw c → MustQ W Q v')
    (khi : ∀ v' : PState, QiS v v' [.rsi] → 63 < c.toNat → v'.m.core.rip = b + 0x5cc0#64 →
      v'.m.core.read .rsi = bw c → MustQ W Q v') : MustQ W Q v := by
  refine must_blkX_at (cb := 0x4f50) blk510b blk510b_ok hd hC.img0 hC.ld0 hC.ro0 (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp [blk510b]
  · rename_i v0 h0 b1 h1
    have e0 := qi_load h0 hc
    have e1 : b1 = decide (63 < c.toNat) := qi_bool h1 (by rw [e0]; exact qi_c510b c hs)
    by_cases hl : 63 < c.toNat
    · refine khi _ ⟨rfl, rfl, rfl, fun r hr => state_read_other (by simpa [blk510b] using hr)⟩ hl ?_ ?_
      · blk_simp [blk510b, hrip, e1, hl]; qi_rip
      · blk_simp [blk510b, e0]; exact qi_rsi c
    · refine klo _ ⟨rfl, rfl, rfl, fun r hr => state_read_other (by simpa [blk510b] using hr)⟩ (by omega) ?_ ?_
      · blk_simp [blk510b, hrip, e1, hl]; qi_rip
      · blk_simp [blk510b, e0]; exact qi_rsi c
  · qi_side
  · exact ⟨_, hc⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem qi_5118 (hd : v.g.done = none) (hC : QiCode W b v.m.memory) (hrip : v.m.core.rip = b + 0x5118#64)
    {c : Byte} (hs : QSafe c) (hrsi : v.m.core.read .rsi = bw c)
    (k : ∀ v' : PState, QiS v v' [] → v'.m.core.rip = b + 0x5121#64 → MustQ W Q v') : MustQ W Q v := by
  refine must_blkX_at (cb := 0x4f50) blk5118 blk5118_ok hd hC.img0 hC.ld0 hC.ro0 (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp [blk5118]
  · rename_i b0 h0
    have e0 : b0 = false := qi_bool h0 (by rw [hrsi]; exact qi_c5118 c hs)
    refine k _ ⟨rfl, rfl, rfl, fun r hr => state_read_other (by simp)⟩ ?_
    blk_simp [blk5118, hrip, e0]; qi_rip
  · qi_side

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem qi_5121 (hd : v.g.done = none) (hC : QiCode W b v.m.memory) (hrip : v.m.core.rip = b + 0x5121#64)
    {c : Byte} (hs : QSafe c) (hl : c.toNat ≤ 63) (hrsi : v.m.core.read .rsi = bw c)
    (k : ∀ v' : PState, QiS v v' [] → v'.m.core.rip = b + 0x512b#64 → MustQ W Q v') : MustQ W Q v := by
  refine must_blkX_at (cb := 0x4f50) blk5121 blk5121_ok hd hC.img0 hC.ld0 hC.ro0 (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp [blk5121]
  · rename_i b0 h0
    have e0 : b0 = false := qi_bool h0 (by rw [hrsi]; exact qi_c5121 c hs hl)
    refine k _ ⟨rfl, rfl, rfl, fun r hr => state_read_other (by simp)⟩ ?_
    blk_simp [blk5121, hrip, e0]; qi_rip
  · qi_side

/-- The jump-table entry of every safe byte `≤ 0x3f` (`%+,-./0-9:`): `0x5165 - 0x7f74`. -/
abbrev qiJ : Word := 0xffffd1f1#64

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem qi_512b (hd : v.g.done = none) (hC : QiCode W b v.m.memory) (hrip : v.m.core.rip = b + 0x512b#64)
    {c : Byte} (hrsi : v.m.core.read .rsi = bw c)
    (hj : loadN v.m.memory (b + BitVec.ofNat 64 (0x7f74 + 4 * c.toNat)) 4 = some qiJ)
    (k : ∀ v' : PState, QiS v v' [.rax, .rdi] → v'.m.core.rip = b + 0x5165#64 → MustQ W Q v') : MustQ W Q v := by
  have ea : v.m.core.rip + 11849#64 + BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64
      (BitVec.setWidth 8 (v.m.core.read Reg.rsi)))) <<< 2 = b + BitVec.ofNat 64 (0x7f74 + 4 * c.toNat) := by
    rw [hrsi, qi_rsi, qi_shl2, hrip]
    have := c.isLt
    bv_omega
  have hj' : loadN v.m.memory (v.m.core.rip + 11849#64 + BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64
      (BitVec.setWidth 8 (v.m.core.read Reg.rsi)))) <<< 2) 4 = some qiJ := by rw [ea]; exact hj
  clear ea hj
  refine must_blkX_at (cb := 0x4f50) blk512b blk512b_ok hd hC.img0 hC.ld0 hC.ro0 (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp [blk512b]
  · rename_i v0 h0
    have e0 := qi_load h0 hj'
    refine k _ ⟨rfl, rfl, rfl, fun r hr => state_read_other (by simpa [blk512b] using hr)⟩ ?_
    blk_simp [blk512b, hrip, e0]; qi_rip
  · exact ⟨_, hj'⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem qi_5cc0 (hd : v.g.done = none) (hC : QiCode W b v.m.memory) (hrip : v.m.core.rip = b + 0x5cc0#64)
    {c : Byte} (hs : QSafe c) (hrsi : v.m.core.read .rsi = bw c)
    (k : ∀ v' : PState, QiS v v' [] → v'.m.core.rip = b + 0x5cc6#64 → MustQ W Q v') : MustQ W Q v := by
  refine must_blkX_at (cb := 0x5cc0) blk5cc0 blk5cc0_ok hd hC.img3 hC.ld3 hC.ro3 (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp [blk5cc0]
  · rename_i b0 h0
    have e0 : b0 = false := qi_bool h0 (by rw [hrsi]; exact qi_c5cc0 c hs)
    refine k _ ⟨rfl, rfl, rfl, fun r hr => state_read_other (by simp)⟩ ?_
    blk_simp [blk5cc0, hrip, e0]; qi_rip
  · qi_side

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem qi_5cc6 (hd : v.g.done = none) (hC : QiCode W b v.m.memory) (hrip : v.m.core.rip = b + 0x5cc6#64)
    {c : Byte} (hs : QSafe c) (hl : 63 < c.toNat) (hrsi : v.m.core.read .rsi = bw c)
    (k : ∀ v' : PState, QiS v v' [] → v'.m.core.rip = b + 0x5cd0#64 → MustQ W Q v') : MustQ W Q v := by
  refine must_blkX_at (cb := 0x5cc0) blk5cc6 blk5cc6_ok hd hC.img3 hC.ld3 hC.ro3 (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp [blk5cc6]
  · rename_i b0 h0
    have e0 : b0 = false := qi_bool h0 (by rw [hrsi]; exact qi_c5cc6 c hs hl)
    refine k _ ⟨rfl, rfl, rfl, fun r hr => state_read_other (by simp)⟩ ?_
    blk_simp [blk5cc6, hrip, e0]; qi_rip
  · qi_side

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem qi_5cd0 (hd : v.g.done = none) (hC : QiCode W b v.m.memory) (hrip : v.m.core.rip = b + 0x5cd0#64)
    {c : Byte} (hs : QSafe c) (hl : 63 < c.toNat) (hrsi : v.m.core.read .rsi = bw c)
    (k : ∀ v' : PState, QiS v v' [.rax, .rcx, .rdx] → v'.m.core.rip = b + 0x5165#64 → MustQ W Q v') :
    MustQ W Q v := by
  refine must_blkX_at (cb := 0x5cc0) blk5cd0 blk5cd0_ok hd hC.img3 hC.ld3 hC.ro3 (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp [blk5cd0]
  · rename_i b0 h0
    have e0 : b0 = true := qi_bool h0 (by rw [hrsi]; exact qi_c5cd0 c hs hl)
    refine k _ ⟨rfl, rfl, rfl, fun r hr => state_read_other (by simpa [blk5cd0] using hr)⟩ ?_
    blk_simp [blk5cd0, hrip, e0]; qi_rip
  · qi_side

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem qi_5165 (hd : v.g.done = none) (hC : QiCode W b v.m.memory) (hrip : v.m.core.rip = b + 0x5165#64)
    (h5d : loadN v.m.memory (v.m.core.read .rbp + 0xffffffffffffffa3#64) 1 = some 1#64)
    (hr8 : (v.m.core.read .r8).setWidth 8 = 0#8)
    (k : ∀ v' : PState, QiS v v' [.rax] → v'.m.core.rip = b + 0x516b#64 →
      Silmaril.X86.Ext.Cond.eval v'.m.core.flags .e = some false → MustQ W Q v') : MustQ W Q v := by
  refine must_blkX_at (cb := 0x5165) blk5165 blk5165_ok hd hC.img1 hC.ld1 hC.ro1 (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp [blk5165]
  · rename_i v0 h0
    have e0 := qi_load h0 h5d
    refine k _ ⟨rfl, rfl, rfl, fun r hr => state_read_other (by simpa [blk5165] using hr)⟩ ?_ ?_
    · blk_simp [blk5165, hrip]
    · blk_simp [blk5165, e0]; simp [hr8]; decide
  · exact ⟨_, h5d⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem qi_516b (hd : v.g.done = none) (hC : QiCode W b v.m.memory) (hrip : v.m.core.rip = b + 0x516b#64)
    (hfl : Silmaril.X86.Ext.Cond.eval v.m.core.flags .e = some false)
    (k : ∀ v' : PState, QiS v v' [] → v'.m.core.rip = b + 0x5171#64 → MustQ W Q v') : MustQ W Q v := by
  refine must_blkX_at (cb := 0x5165) blk516b blk516b_ok hd hC.img1 hC.ld1 hC.ro1 (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp [blk516b]
  · rename_i b0 h0
    have e0 : b0 = false := qi_bool h0 hfl
    refine k _ ⟨rfl, rfl, rfl, fun r hr => state_read_other (by simp)⟩ ?_
    blk_simp [blk516b, hrip, e0]; qi_rip
  · exact ⟨_, hfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem qi_5171 (hd : v.g.done = none) (hC : QiCode W b v.m.memory) (hrip : v.m.core.rip = b + 0x5171#64)
    {A : Word} (h80 : loadN v.m.memory (v.m.core.read .rbp + 0xffffffffffffff80#64) 8 = some A) (hA : A ≠ 0#64)
    (k : ∀ v' : PState, QiS v v' [.rax, .rcx] → v'.m.core.rip = b + 0x5180#64 →
      v'.m.core.read .rax = 0#64 → v'.m.core.read .rcx = A → MustQ W Q v') : MustQ W Q v := by
  refine must_blkX_at (cb := 0x5165) blk5171 blk5171_ok hd hC.img1 hC.ld1 hC.ro1 (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp [blk5171]
  · rename_i v0 h0 b1 h1
    have e0 := qi_load h0 h80
    have e1 : b1 = false := qi_bool h1 (by
      rw [e0]; simp [Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.logicFlagsN, Silmaril.X86.Ext.isZeroN, hA])
    refine k _ ⟨rfl, rfl, rfl, fun r hr => state_read_other (by simpa [blk5171] using hr)⟩ ?_ ?_ ?_
    · blk_simp [blk5171, hrip, e1]; qi_rip
    · blk_simp [blk5171]; simp
    · blk_simp [blk5171, e0]
  · qi_side
  · exact ⟨_, h80⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem qi_5180 (hd : v.g.done = none) (hC : QiCode W b v.m.memory) (hrip : v.m.core.rip = b + 0x5180#64)
    {c : Byte} (hrsi : v.m.core.read .rsi = bw c)
    (k : ∀ v' : PState, QiS v v' [.rdx] → v'.m.core.rip = b + 0x5185#64 →
      (v'.m.core.read .rdx).setWidth 8 = BitVec.ofNat 8 (c.toNat / 32) → MustQ W Q v') : MustQ W Q v := by
  refine must_blkX_at (cb := 0x5165) blk5180 blk5180_ok hd hC.img1 hC.ld1 hC.ro1 (by rw [hrip]; rfl) ?_
  blk_wp
  blk_simp [blk5180]
  refine k _ ⟨rfl, rfl, rfl, fun r hr => state_read_other (by simpa [blk5180] using hr)⟩ ?_ ?_
  · blk_simp [blk5180, hrip]
  · blk_simp [blk5180]; rw [qi_m8, hrsi]; qi_dec c

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem qi_5185 (hd : v.g.done = none) (hC : QiCode W b v.m.memory) (hrip : v.m.core.rip = b + 0x5185#64)
    {c : Byte} (hs : QSafe c) (hrsi : v.m.core.read .rsi = bw c) {A : Word} (hrcx : v.m.core.read .rcx = A)
    (hrdx : (v.m.core.read .rdx).setWidth 8 = BitVec.ofNat 8 (c.toNat / 32))
    (hq : loadN v.m.memory (A + BitVec.ofNat 64 (4 * (c.toNat / 32))) 4 = some (qiQ c))
    (k : ∀ v' : PState, QiS v v' [.rcx, .rdx] → v'.m.core.rip = b + 0x5248#64 → MustQ W Q v') :
    MustQ W Q v := by
  have hq' : loadN v.m.memory (v.m.core.read Reg.rcx + BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64
      (BitVec.setWidth 8 (v.m.core.read Reg.rdx)))) <<< 2) 4 = some (qiQ c) := by
    rw [hrcx, hrdx, qi_a5185]; exact hq
  clear hq hrcx hrdx
  refine must_blkX_at (cb := 0x5165) blk5185 blk5185_ok hd hC.img1 hC.ld1 hC.ro1 (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp [blk5185]
  · rename_i v0 h0 b1 h1
    have e0 := qi_load h0 hq'
    have e1 : b1 = true := qi_bool h1 (by rw [e0, hrsi]; exact qi_c5185 c hs)
    refine k _ ⟨rfl, rfl, rfl, fun r hr => state_read_other (by simpa [blk5185] using hr)⟩ ?_
    blk_simp [blk5185, hrip, e1]; qi_rip
  · qi_side
  · exact ⟨_, hq'⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem qi_5248 (hd : v.g.done = none) (hC : QiCode W b v.m.memory) (hrip : v.m.core.rip = b + 0x5248#64)
    (h5c : loadN v.m.memory (v.m.core.read .rbp + 0xffffffffffffffa4#64) 4 = some 2#64)
    (hr12 : (v.m.core.read .r12).setWidth 8 = 0#8)
    (k : ∀ v' : PState, QiS v v' [.rdx] → v'.m.core.rip = b + 0x5258#64 → MustQ W Q v') : MustQ W Q v := by
  refine must_blkX_at (cb := 0x5165) blk5248 blk5248_ok hd hC.img1 hC.ld1 hC.ro1 (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp [blk5248]
  · rename_i v0 h0 b1 h1 b2 h2
    have e2 : b2 = false := qi_bool h2 (by rw [hr12]; decide)
    refine k _ ⟨rfl, rfl, rfl, fun r hr => state_read_other (by simpa [blk5248] using hr)⟩ ?_
    blk_simp [blk5248, hrip, e2]; qi_rip
  · qi_side
  · qi_side
  · exact ⟨_, h5c⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem qi_5258 (hd : v.g.done = none) (hC : QiCode W b v.m.memory) (hrip : v.m.core.rip = b + 0x5258#64)
    (h5e : loadN v.m.memory (v.m.core.read .rbp + 0xffffffffffffffa2#64) 1 = some 0#64)
    (k : ∀ v' : PState, QiS v v' [.rax, .rbx] → v'.m.core.rip = b + 0x5262#64 →
      (v'.m.core.read .rax).setWidth 8 = 0#8 → v'.m.core.read .rbx = v.m.core.read .rbx + 1#64 →
      MustQ W Q v') : MustQ W Q v := by
  refine must_blkX_at (cb := 0x5165) blk5258 blk5258_ok hd hC.img1 hC.ld1 hC.ro1 (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp [blk5258]
  · rename_i v0 h0
    have e0 := qi_load h0 h5e
    refine k _ ⟨rfl, rfl, rfl, fun r hr => state_read_other (by simpa [blk5258] using hr)⟩ ?_ ?_ ?_
    · blk_simp [blk5258, hrip]
    · blk_simp [blk5258, e0]; rw [qi_m8]; simp
    · blk_simp [blk5258]
  · exact ⟨_, h5e⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem qi_5262 (hd : v.g.done = none) (hC : QiCode W b v.m.memory) (hrip : v.m.core.rip = b + 0x5262#64)
    (hax : (v.m.core.read .rax).setWidth 8 = 0#8)
    (k : ∀ v' : PState, QiS v v' [] → v'.m.core.rip = b + 0x5207#64 → MustQ W Q v') : MustQ W Q v := by
  refine must_blkX_at (cb := 0x5165) blk5262 blk5262_ok hd hC.img1 hC.ld1 hC.ro1 (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp [blk5262]
  · rename_i b0 h0
    have e0 : b0 = true := qi_bool h0 (by rw [hax]; decide)
    refine k _ ⟨rfl, rfl, rfl, fun r hr => state_read_other (by simp)⟩ ?_
    blk_simp [blk5262, hrip, e0]; qi_rip
  · qi_side

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem qi_5207 (hd : v.g.done = none) (hC : QiCode W b v.m.memory) (hrip : v.m.core.rip = b + 0x5207#64)
    {i : Nat} (hi : i < 256)
    (hlen : loadN v.m.memory (v.m.core.read .rbp + 0xffffffffffffffa8#64) 8 = some (BitVec.ofNat 64 i))
    (hr11 : v.m.core.read .r11 = 256#64)
    (k : ∀ v' : PState, QiS v v' [.rax] → v'.m.core.rip = b + 0x5210#64 →
      v'.m.core.read .rax = BitVec.ofNat 64 i → MustQ W Q v') : MustQ W Q v := by
  refine must_blkX_at (cb := 0x5165) blk5207 blk5207_ok hd hC.img1 hC.ld1 hC.ro1 (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp [blk5207]
  · rename_i v0 h0 b1 h1
    have e0 := qi_load h0 hlen
    have hu : (BitVec.ofNat 64 i).ult 256#64 = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
    have e1 : b1 = false := qi_bool h1 (by
      rw [e0, hr11]
      simp only [Silmaril.X86.Ext.AluOp.flagsN, BitVec.setWidth_eq, eval_ae_sub, hu]; rfl)
    refine k _ ⟨rfl, rfl, rfl, fun r hr => state_read_other (by simpa [blk5207] using hr)⟩ ?_ ?_
    · blk_simp [blk5207, hrip, e1]; qi_rip
    · blk_simp [blk5207, e0]
  · qi_side
  · exact ⟨_, hlen⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem qi_5210 (hd : v.g.done = none) (hC : QiCode W b v.m.memory) (hrip : v.m.core.rip = b + 0x5210#64)
    {c : Byte} (hrsi : v.m.core.read .rsi = bw c)
    (hw : v.m.memory.Permitted .write (v.m.core.read .r9 + v.m.core.read .rax).toNat 1)
    (k : ∀ v' : PState, v'.m.memory = storeMem v.m.memory (v.m.core.read .r9 + v.m.core.read .rax) 1 (bw c) →
      v'.g = v.g → v'.m.core.fsBase = v.m.core.fsBase → (∀ r, v'.m.core.read r = v.m.core.read r) →
      v'.m.core.rip = b + 0x5214#64 → MustQ W Q v') : MustQ W Q v := by
  refine must_blkX_at (cb := 0x5165) blk5210 blk5210_ok hd hC.img1 hC.ld1 hC.ro1 (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp [blk5210]
  · refine k _ ?_ rfl rfl (fun r => state_read_other (by simp)) ?_
    · blk_simp [blk5210, hrsi, qi_z8]
    · blk_simp [blk5210, hrip]
  · exact hw

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem qi_5214 (hd : v.g.done = none) (hC : QiCode W b v.m.memory) (hrip : v.m.core.rip = b + 0x5214#64)
    {x L : Word}
    (hpend : loadN v.m.memory (v.m.core.read .rbp + 0xffffffffffffff98#64) 1 = some x)
    (hlen : loadN v.m.memory (v.m.core.read .rbp + 0xffffffffffffffa8#64) 8 = some L)
    (hw1 : v.m.memory.Permitted .write (v.m.core.read .rbp + 0xffffffffffffffa8#64).toNat 8)
    (hw2 : v.m.memory.Permitted .write (v.m.core.read .rbp + 0xffffffffffffff98#64).toNat 1)
    (k : ∀ v' : PState, (∃ y, v'.m.memory = storeMem (storeMem v.m.memory
        (v.m.core.read .rbp + 0xffffffffffffffa8#64) 8 (L + 1#64)) (v.m.core.read .rbp + 0xffffffffffffff98#64) 1 y) →
      v'.g = v.g → v'.m.core.fsBase = v.m.core.fsBase →
      (∀ r, r ∉ [Reg.rax, Reg.rdi] → v'.m.core.read r = v.m.core.read r) →
      v'.m.core.rip = b + 0x50c0#64 → MustQ W Q v') : MustQ W Q v := by
  refine must_blkX_at (cb := 0x5165) blk5214 blk5214_ok hd hC.img1 hC.ld1 hC.ro1 (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp [blk5214]
  · rename_i v0 h0 v1 h1 b2 h2
    have e1 := qi_load h1 hlen
    refine k _ ?_ rfl rfl (fun r hr => state_read_other (by simpa [blk5214] using hr)) ?_
    · blk_simp [blk5214, e1]; exact ⟨_, rfl⟩
    · blk_simp [blk5214, hrip]; qi_rip
  · exact hw2
  · qi_side
  · exact hw1
  · exact ⟨_, hlen⟩
  · exact ⟨_, hpend⟩

end Silmaril.Elf.Link.Dyn.Sha256sum
