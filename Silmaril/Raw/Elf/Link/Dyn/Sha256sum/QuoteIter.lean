module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.QuoteIterSeg
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.QuoteCells

/-! # GNU `sha256sum`: one safe byte of `quotearg_buffer_restyled`'s loop (`Task.quoteIter`)

**`task_quoteIter`**: from the loop invariant `QLoop … i` at `0x50c0` with `i < |p|`, the four
segments of `QuoteIterSeg` reach `0x50c0` again with `QLoop … (i + 1)`: `slot0[i]` holds the
`i`-th byte of the name, `len = i + 1`, `rbx = i + 1`, the stack cells (`QStk`) and the frame
(`QF`) kept. The memory facts the blocks need come from `QLoop`/`QEntry`: the name byte (kept
memory outside `slot0`), the option cells of the run's stack, the byte jump table at `0x7f74`
(read-only data, `ShaRO`: entry `0x5165` for every safe byte `≤ 0x3f`) and `quote_these_too`. -/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Cert
open Silmaril.Elf.Link.Dyn.Streams

set_option maxRecDepth 10000 in
theorem qi_lens : quoteX0Text.length = 496 ∧ quoteX1Text.length = 257 ∧ quoteX3Text.length = 46 := by
  decide

theorem ShaRO.qiCode {W : World} {b lb : Word} {M : Memory} (h : ShaRO b lb M) (I : W.InImage = ShaImg b)
    (hb : b.toNat + 0xa188 < 2 ^ 64) : QiCode W b M := by
  have q0 := h.qc (W := W) I hb (cb := 0x4f50) (by omega) (by rw [qi_lens.1]; omega) (by rw [qi_lens.1]; omega)
    quoteX0_plain
  have q1 := h.qc (W := W) I hb (cb := 0x5165) (by omega) (by rw [qi_lens.2.1]; omega)
    (by rw [qi_lens.2.1]; omega) quoteX1_plain
  have q3 := h.qc (W := W) I hb (cb := 0x5cc0) (by omega) (by rw [qi_lens.2.2]; omega)
    (by rw [qi_lens.2.2]; omega) quoteX3_plain
  exact ⟨q0.img, q0.ld, q0.ro, q1.img, q1.ld, q1.ro, q3.img, q3.ld, q3.ro⟩

/-- The four bytes of the jump-table entry `0x5165 - 0x7f74`. -/
def qiJB : List Byte := ([0xf1, 0xd1, 0xff, 0xff] : List Nat).map (BitVec.ofNat 8)

/-- **The byte jump table** (`0x7f74`, `.rodata`): every safe byte `≤ 0x3f` (`%+,-./0-9`) goes to
`0x5165`. -/
theorem qi_jt_plain : ∀ n, n < 64 → QSafe (BitVec.ofNat 8 n) →
    plainOk shaFile shaRoPh shaSlots (0x7f74 + 4 * n) qiJB = true := by
  decide +kernel

theorem qi_jt {b lb : Word} {M : Memory} (h : ShaRO b lb M) (hb : b.toNat + 0xa188 < 2 ^ 64) {c : Byte}
    (hs : QSafe c) (hl : c.toNat ≤ 63) :
    loadN M (b + BitVec.ofNat 64 (0x7f74 + 4 * c.toNat)) 4 = some qiJ := by
  have hp := qi_jt_plain c.toNat (by omega) (by simpa using hs)
  have := h.readRo hb (v := 0x7f74 + 4 * c.toNat) (l := qiJB) (by omega) (by simp [qiJB]; omega)
    (by simp [qiJB]) hp
  rw [show qiJB.length = 4 from rfl] at this
  rw [Silmaril.X86.Ext.loadN_of_readBytes this]
  decide

theorem qi_kl {M M' : Memory} {P : Nat → Prop} (hk : Keeps P M M') {R : Word} {d n : Nat} (hd : d ≤ R.toNat)
    (hP : ∀ j, j < n → P (R.toNat - d + j)) {x : Word} (h : loadN M (R - BitVec.ofNat 64 d) n = some x) :
    loadN M' (R - BitVec.ofNat 64 d) n = some x := by
  rw [hk.loadN (fun j hj => by rw [bsub_toNat hd]; exact hP j hj)]; exact h

/-- The cells of `QStk` (below `R`, outside `len` and the pending byte). -/
def QiStkP (R : Word) (a : Nat) : Prop :=
  R.toNat - 0x190 ≤ a ∧ a < R.toNat ∧ ¬ (R.toNat - 0x140 ≤ a ∧ a < R.toNat - 0x13f) ∧
    ¬ (R.toNat - 0x130 ≤ a ∧ a < R.toNat - 0x128)

set_option maxRecDepth 10000 in
theorem QStk.qiKeep {E : Env} {b : Word} {s : PState} {g ev : Word} {M M' : Memory}
    (h : QStk E b s g ev M) (h4 : 2048 ≤ (s.m.core.read .rsp).toNat)
    (hk : Keeps (QiStkP (s.m.core.read .rsp)) M M') : QStk E b s g ev M' := by
  constructor
  · exact qi_kl hk (d := 0x8) (by omega) (fun j hj => by unfold QiStkP; omega) h.f8
  · exact qi_kl hk (d := 0x10) (by omega) (fun j hj => by unfold QiStkP; omega) h.f10
  · exact qi_kl hk (d := 0x3c) (by omega) (fun j hj => by unfold QiStkP; omega) h.q1
  · exact qi_kl hk (d := 0x38) (by omega) (fun j hj => by unfold QiStkP; omega) h.q2
  · exact qi_kl hk (d := 0x34) (by omega) (fun j hj => by unfold QiStkP; omega) h.q3
  · exact qi_kl hk (d := 0x50) (by omega) (fun j hj => by unfold QiStkP; omega) h.f50
  · exact qi_kl hk (d := 0x58) (by omega) (fun j hj => by unfold QiStkP; omega) h.f58
  · exact qi_kl hk (d := 0x60) (by omega) (fun j hj => by unfold QiStkP; omega) h.f60
  · exact qi_kl hk (d := 0x68) (by omega) (fun j hj => by unfold QiStkP; omega) h.f68
  · exact qi_kl hk (d := 0x70) (by omega) (fun j hj => by unfold QiStkP; omega) h.f70
  · exact qi_kl hk (d := 0x78) (by omega) (fun j hj => by unfold QiStkP; omega) h.f78
  · exact qi_kl hk (d := 0x80) (by omega) (fun j hj => by unfold QiStkP; omega) h.f80
  · rw [hk.readBytes (fun j hj => by rw [bsub_toNat (d := 0x94) (by omega)]; unfold QiStkP; omega)]; exact h.f94
  · exact qi_kl hk (d := 0xc0) (by omega) (fun j hj => by unfold QiStkP; omega) h.fc0
  · exact qi_kl hk (d := 0xc8) (by omega) (fun j hj => by unfold QiStkP; omega) h.fc8
  · exact qi_kl hk (d := 0xd0) (by omega) (fun j hj => by unfold QiStkP; omega) h.fd0
  · exact qi_kl hk (d := 0xd8) (by omega) (fun j hj => by unfold QiStkP; omega) h.fd8
  · exact qi_kl hk (d := 0xe0) (by omega) (fun j hj => by unfold QiStkP; omega) h.fe0
  · exact qi_kl hk (d := 0xe8) (by omega) (fun j hj => by unfold QiStkP; omega) h.fe8
  · exact qi_kl hk (d := 0xf0) (by omega) (fun j hj => by unfold QiStkP; omega) h.ff0
  · exact qi_kl hk (d := 0xf8) (by omega) (fun j hj => by unfold QiStkP; omega) h.ff8
  · exact qi_kl hk (d := 0x100) (by omega) (fun j hj => by unfold QiStkP; omega) h.f100
  · exact qi_kl hk (d := 0x110) (by omega) (fun j hj => by unfold QiStkP; omega) h.f110
  · exact qi_kl hk (d := 0x134) (by omega) (fun j hj => by unfold QiStkP; omega) h.f134
  · exact qi_kl hk (d := 0x135) (by omega) (fun j hj => by unfold QiStkP; omega) h.f135
  · exact qi_kl hk (d := 0x136) (by omega) (fun j hj => by unfold QiStkP; omega) h.f136
  · exact qi_kl hk (d := 0x137) (by omega) (fun j hj => by unfold QiStkP; omega) h.f137
  · exact qi_kl hk (d := 0x148) (by omega) (fun j hj => by unfold QiStkP; omega) h.f148
  · exact qi_kl hk (d := 0x150) (by omega) (fun j hj => by unfold QiStkP; omega) h.f150
  · exact qi_kl hk (d := 0x158) (by omega) (fun j hj => by unfold QiStkP; omega) h.f158
  · exact qi_kl hk (d := 0x190) (by omega) (fun j hj => by unfold QiStkP; omega) h.f190

theorem qi_bsz (c : Byte) : Silmaril.X86.Ext.leBytes (bw c) 1 = [c] := by
  revert c; apply qi_all; decide +kernel

theorem qi_perm_of {m : Memory} {acc : Access} {a len : Nat} (h1 : a + len < 2 ^ 64)
    (h : ∀ k, k < len → m.permits acc (a + k) = true) : m.Permitted acc a len := by
  rw [Memory.Permitted, Memory.checkSpan_iff]
  simp only [Silmaril.Process.addressLimit]
  exact ⟨by omega, by omega, h⟩

theorem qi_loadN_one {m : Memory} {a : Word} {x : Byte} (h : m.readBytes a.toNat 1 = some [x]) :
    loadN m a 1 = some (bw x) := by
  simp [loadN, h, Silmaril.X86.Ext.leValue]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`Task.quoteIter`**: one safe byte of the loop, `QLoop i` to `QLoop (i + 1)`. -/
theorem task_quoteIter {E : Env} {W : World} {b lb : Word} : Task.quoteIter E W b lb := by
  intro s w p g ev i hE hpl hL hi
  have hfit : p.length < 256 := by
    have := hE.fits
    rwa [FilesSpec.quotef_plain _ (by simpa [toSpec] using hpl.1) hpl.2, toSpec, List.length_map] at this
  have hroom := hE.room
  have h4 : 2048 ≤ (s.m.core.read .rsp).toNat := hroom.1
  have hR8 := hroom.2.1
  have hb := hE.imps.hb
  have I := hE.imps.img
  have hF := hL.F
  have hroomM : Room W w.m.memory (s.m.core.read .rsp) 2048 := hF.room hroom
  have hro : ShaRO b lb w.m.memory := QF.shaRO hE hF
  have hC : QiCode W b w.m.memory := hro.qiCode I hb
  have hd : w.g.done = none := by rw [hL.gh]; exact hE.done
  obtain ⟨c, hcd⟩ : ∃ c, p[i] = c := ⟨_, rfl⟩
  have hs : QSafe c := hpl.2 _ (by rw [toSpec, ← hcd]; exact List.mem_map_of_mem (List.getElem_mem hi))
  set R := s.m.core.read .rsp with hR
  have hrbp : w.m.core.read .rbp = R - 0xd8#64 := hL.rbp
  have hS := hL.stk
  -- the name byte
  have hname := hE.name.2
  have hbound := permitted_bound (Memory.readWith_permitted hname)
  have hnb : s.m.memory.readBytes ((s.m.core.read .rdi).toNat + i) 1 = some [c] := by
    rw [Memory.readBytes_sub_range hname (offset := i) (len := 1) (by simp; omega) (by simp; omega),
      List.drop_append_of_le_length (by omega), List.drop_eq_getElem_cons hi, hcd]
    simp
  have hnbM : w.m.memory.readBytes ((s.m.core.read .rdi).toNat + i) 1 = some [c] := by
    rw [(hF.keepK hroom).readBytes (fun j hj => by
      have := hE.namek (i + j) (by omega); rwa [← Nat.add_assoc] at this)]; exact hnb
  have ha : (s.m.core.read .rdi + BitVec.ofNat 64 i).toNat = (s.m.core.read .rdi).toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega), Nat.mod_eq_of_lt (by omega)]
  have hc8 : loadN w.m.memory (s.m.core.read .rdi + w.m.core.read .rbx) 1 = some (bw c) := by
    rw [hL.rbx]; exact qi_loadN_one (by rw [ha]; exact hnbM)
  -- slot0
  have hSn : (b + 0xa060#64 + BitVec.ofNat 64 i).toNat = b.toNat + 0xa060 + i := by
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have hB0 : (b + 0xa060#64).toNat = b.toNat + 0xa060 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hSl : Slot0 b (b.toNat + 0xa060 + i) := by unfold Slot0; omega
  have hSimg : ∀ j, j < i + 1 → ShaImg b (b.toNat + 0xa060 + j) := fun j hj => by unfold ShaImg; omega
  have hnotstk : ∀ x, R.toNat - 2048 ≤ x → x < R.toNat → x ≠ b.toNat + 0xa060 + i := by
    intro x h1 h2 hx
    have := (hroom.2.2 x (by omega) (by omega)).2.2
    exact this (Or.inl (by rw [I, hx]; exact hSimg i (by omega)))
  have hdisj : ∀ lo hi', R.toNat - 2048 ≤ lo → hi' ≤ R.toNat → lo < hi' →
      b.toNat + 0xa060 + (i + 1) ≤ lo ∨ hi' ≤ b.toNat + 0xa060 := fun lo hi' h1 h2 h3 =>
    img_room hroom I (a := b.toNat + 0xa060) (k := i + 1) hSimg (by omega)
      (by omega) (by omega) h3
  -- the option cells (rbp-relative)
  have e90 : R - 0xd8#64 + 0xffffffffffffff90#64 = R - 0x148#64 := by bv_omega
  have ea4 : R - 0xd8#64 + 0xffffffffffffffa4#64 = R - 0x134#64 := by bv_omega
  have ea1 : R - 0xd8#64 + 0xffffffffffffffa1#64 = R - 0x137#64 := by bv_omega
  have e88 : R - 0xd8#64 + 0xffffffffffffff88#64 = R - 0x150#64 := by bv_omega
  have ea3 : R - 0xd8#64 + 0xffffffffffffffa3#64 = R - 0x135#64 := by bv_omega
  have e80 : R - 0xd8#64 + 0xffffffffffffff80#64 = R - 0x158#64 := by bv_omega
  have ea2 : R - 0xd8#64 + 0xffffffffffffffa2#64 = R - 0x136#64 := by bv_omega
  have ea8 : R - 0xd8#64 + 0xffffffffffffffa8#64 = R - 0x130#64 := by bv_omega
  have e98 : R - 0xd8#64 + 0xffffffffffffff98#64 = R - 0x140#64 := by bv_omega
  have hA : R - 0x40#64 ≠ 0#64 := by bv_omega
  have hq : loadN w.m.memory (R - 0x40#64 + BitVec.ofNat 64 (4 * (c.toNat / 32))) 4 = some (qiQ c) := by
    have hl := qi_lt c hs
    unfold qiQ
    rcases (by omega : c.toNat / 32 = 1 ∨ c.toNat / 32 = 2 ∨ c.toNat / 32 = 3) with h | h | h <;> rw [h]
    · rw [show R - 0x40#64 + BitVec.ofNat 64 (4 * 1) = R - 0x3c#64 by bv_omega]; exact hS.q1
    · rw [show R - 0x40#64 + BitVec.ofNat 64 (4 * 2) = R - 0x38#64 by bv_omega]; exact hS.q2
    · rw [show R - 0x40#64 + BitVec.ofNat 64 (4 * 3) = R - 0x34#64 by bv_omega]; exact hS.q3
  -- segment A
  refine qi_segA (v := w) hd hC hL.rip hL.r14 hs (nm := s.m.core.read .rdi)
    (by rw [hrbp, e90]; exact hS.f148) hc8 (by rw [hrbp, ea4]; exact hS.f134)
    (by rw [hrbp, ea1]; exact hS.f137) (by rw [hrbp, e88]; exact hS.f150)
    fun vA SA rA h10A h12A h8A hcxA => ?_
  refine qi_segB (SA.done hd) (SA.code hC) rA hs (by rw [SA.1, hcxA]; exact hc8)
    (fun hl => by rw [SA.1]; exact qi_jt hro hb hs hl) fun vB SB rB hsiB => ?_
  have SAB := SA.trans SB
  have rbB : vB.m.core.read .rbp = R - 0xd8#64 := by rw [SAB.2.2.2 .rbp (by decide), hrbp]
  refine qi_segC (SAB.done hd) (SAB.code hC) rB hs hsiB (by rw [SB.2.2.2 .r8 (by decide)]; exact h8A)
    (by rw [SB.2.2.2 .r12 (by decide)]; exact h12A) hA (by rw [SAB.1, rbB, ea3]; exact hS.f135)
    (by rw [SAB.1, rbB, e80]; exact hS.f158) (by rw [SAB.1]; exact hq)
    (by rw [SAB.1, rbB, ea4]; exact hS.f134) (by rw [SAB.1, rbB, ea2]; exact hS.f136)
    fun vC SC rC hbxC hsiC => ?_
  have SABC := SAB.trans SC
  have rbC : vC.m.core.read .rbp = R - 0xd8#64 := by rw [SABC.2.2.2 .rbp (by decide), hrbp]
  have r9C : vC.m.core.read .r9 = b + 0xa060#64 := by rw [SABC.2.2.2 .r9 (by decide), hL.r9]
  have mC : vC.m.memory = w.m.memory := SABC.1
  obtain ⟨x, hx⟩ := hL.pend
  have hwS : w.m.memory.Permitted .write (b + 0xa060#64 + BitVec.ofNat 64 i).toNat 1 := by
    rw [hSn]
    refine qi_perm_of (by omega) fun k hk => ?_
    have hk0 : k = 0 := by omega
    subst hk0
    have h1 := hE.slot0 _ hSl
    rw [Nat.add_zero, hF.perm _ h1.2.2 h1.1 .write]; exact h1.2.1
  have hrS : w.m.memory.Permitted .read (b + 0xa060#64 + BitVec.ofNat 64 i).toNat 1 := by
    rw [hSn]
    refine qi_perm_of (by omega) fun k hk => ?_
    have hk0 : k = 0 := by omega
    subst hk0
    have h1 := hE.slot0 _ hSl
    rw [Nat.add_zero, hF.perm _ h1.2.2 h1.1 .read]; exact h1.1
  have t130 : (R - 0x130#64).toNat = R.toNat - 0x130 := bsub_toNat (by omega)
  have t140 : (R - 0x140#64).toNat = R.toNat - 0x140 := bsub_toNat (by omega)
  have hw130 : ∀ acc, acc = .read ∨ acc = .write → w.m.memory.Permitted acc (R - 0x130#64).toNat 8 :=
    fun acc hacc => room_perm hroomM hacc (by omega) (by omega)
  have hw140 : ∀ acc, acc = .read ∨ acc = .write → w.m.memory.Permitted acc (R - 0x140#64).toNat 1 :=
    fun acc hacc => room_perm hroomM hacc (by omega) (by omega)
  have hd130 := hdisj (R.toNat - 0x130) (R.toNat - 0x128) (by omega) (by omega) (by omega)
  have hd140 := hdisj (R.toNat - 0x140) (R.toNat - 0x13f) (by omega) (by omega) (by omega)
  refine qi_segD (i := i) (SABC.done hd) (SABC.code hC)
    (fun y => by rw [mC, r9C]; exact (hro.keep (storeMem_keeps fun x hx => by rw [hSn]; omega)).qiCode I hb)
    rC hsiC (by omega) (x := x)
    (by rw [mC, rbC, ea8]; exact hL.len) (by rw [mC, rbC, e98]; exact hx)
    (by rw [SABC.2.2.2 .r11 (by decide)]; exact hL.r11)
    (by rw [mC, r9C]; exact hwS) (by rw [mC, rbC, ea8]; exact hw130 _ (Or.inr rfl))
    (by rw [mC, rbC, e98]; exact hw140 _ (Or.inr rfl))
    (by rw [r9C, rbC, ea8, hSn, t130]; omega) (by rw [r9C, rbC, e98, hSn, t140]; omega)
    fun v' hm' hg' hf' hr' r' => ?_
  rw [mC, r9C, rbC, ea8, e98] at hm'
  obtain ⟨y, hm'⟩ := hm'
  have reg : ∀ r, r ∉ [Reg.rax, Reg.rdi] → r ∉ qiA → r ∉ qiB → r ∉ qiC →
      v'.m.core.read r = w.m.core.read r := fun r h1 h2 h3 h4 => by
    rw [hr' r h1, SC.2.2.2 r h4, SB.2.2.2 r h3, SA.2.2.2 r h2]
  -- the memory after the three stores
  generalize hS1 : storeMem w.m.memory (b + 0xa060#64 + BitVec.ofNat 64 i) 1 (bw c) = M1 at hm'
  generalize hS2 : storeMem M1 (R - 0x130#64) 8 (BitVec.ofNat 64 i + 1#64) = M2 at hm'
  refine must_done ⟨r', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega, hL.guard, hL.ebytes, hL.ecell⟩
  · rw [reg .rsp (by decide) (by decide) (by decide) (by decide)]; exact hL.rsp
  · rw [reg .rbp (by decide) (by decide) (by decide) (by decide)]; exact hL.rbp
  · rw [hr' .rbx (by decide), hbxC, SB.2.2.2 .rbx (by decide), SA.2.2.2 .rbx (by decide), hL.rbx,
      BitVec.ofNat_add]
  · rw [reg .r9 (by decide) (by decide) (by decide) (by decide)]; exact hL.r9
  · rw [reg .r11 (by decide) (by decide) (by decide) (by decide)]; exact hL.r11
  · rw [reg .r14 (by decide) (by decide) (by decide) (by decide)]; exact hL.r14
  · rw [hf', SC.2.2.1, SB.2.2.1, SA.2.2.1]; exact hL.fs
  · rw [hg', SC.2.1, SB.2.1, SA.2.1]; exact hL.gh
  · -- QStk
    rw [hm']
    refine hS.qiKeep h4 ?_
    rw [← hR, ← hS2, ← hS1]
    refine (storeMem_keeps fun x hx => ?_).trans ((storeMem_keeps fun x hx => ?_).trans
      (storeMem_keeps fun x hx => ?_))
    · rw [hSn]; unfold QiStkP at hx
      have := hnotstk x (by omega) (by omega); omega
    · rw [t130]; unfold QiStkP at hx; omega
    · rw [t140]; unfold QiStkP at hx; omega
  · -- len
    rw [hm', ← hR, loadN_storeMem_ne (by rw [t130, t140]; omega), ← hS2,
      loadN_storeMem_same (by rw [← hS1]; exact storeMem_permitted.2 (hw130 _ (Or.inl rfl))) (BitVec.isLt _), BitVec.ofNat_add]
  · -- the pending byte
    rw [hm', ← hR]
    have hp2 : M2.Permitted .read (R - 0x140#64).toNat 1 := by
      rw [← hS2, ← hS1]; exact storeMem_permitted.2 (storeMem_permitted.2 (hw140 _ (Or.inl rfl)))
    exact ⟨_, by simp only [loadN, storeMem_read hp2, Option.map_some]; rfl⟩
  · -- slot0[0..i]
    rw [hm', storeMem_read_ne (by rw [t140, hB0]; omega), ← hS2, storeMem_read_ne (by rw [t130, hB0]; omega),
      ← hS1, hB0]
    have hx1 : (storeMem w.m.memory (b + 0xa060#64 + BitVec.ofNat 64 i) 1 (bw c)).readBytes
        (b.toNat + 0xa060) i = some (p.take i) := by
      rw [storeMem_read_ne (by rw [hSn]; omega), ← hB0]; exact hL.pre
    have hy1 : (storeMem w.m.memory (b + 0xa060#64 + BitVec.ofNat 64 i) 1 (bw c)).readBytes
        (b.toNat + 0xa060 + i) 1 = some [c] := by
      rw [← hSn, storeMem_read hrS, qi_bsz]
    rw [Memory.readBytes_append hx1 hy1, List.take_add_one, List.getElem?_eq_getElem hi, hcd]
    rfl
  · -- the frame
    rw [hm', ← hS2, ← hS1]
    have F1 : QF E W b s (storeMem w.m.memory (b + 0xa060#64 + BitVec.ofNat 64 i) 1 (bw c)) :=
      hF.local (fun a ha => ⟨(hE.slot0 a ha).2.2, (hE.slot0 a ha).1⟩) hE.lo
        (storeMem_keeps fun x hx => by
          rw [hSn]; by_contra hc; apply hx; left; have : x = b.toNat + 0xa060 + i := by omega
          rw [this]; exact hSl)
        (storeMem_keeps fun x hx => by
          rw [hSn]; by_contra hc
          have hx' : x = b.toNat + 0xa060 + i := by omega
          unfold ErrnoR at hx
          have := hL.ecell.2.2 (x - E.errnoA.toNat) (by omega)
          rw [show E.errnoA.toNat + (x - E.errnoA.toNat) = x by omega, I, hx'] at this
          exact this (hSimg i (by omega)))
        rfl
    have F2 := QF.stores hE F1 (keeps_outStk (d := 0x130) (k := 8) (v := BitVec.ofNat 64 i + 1#64) (by omega) (by omega) h4) rfl
    have F3 := QF.stores hE F2 (keeps_outStk (d := 0x140) (k := 1) (v := y) (by omega) (by omega) h4) rfl
    exact F3

end Silmaril.Elf.Link.Dyn.Sha256sum
