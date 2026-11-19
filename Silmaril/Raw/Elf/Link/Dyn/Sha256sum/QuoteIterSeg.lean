module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.QuoteIterBlk

/-! # GNU `sha256sum`: one iteration of the loop, in four segments

The blocks of `QuoteIterBlk` chained: `qi_segA` (`0x50c0` → `0x510b`: the byte is not NUL,
`r10b = 1`, `r12b = r8b = 0`, `rcx = name + i`), `qi_segB` (`0x510b` → `0x5165`: the byte
class, `rsi = c`), `qi_segC` (`0x5165` → `0x5207`: no quoting, `rbx = i + 1`), `qi_segD`
(`0x5207` → `0x50c0`: `slot0[i] = c`, `len = i + 1`). Registers outside `qiAll` are kept. -/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Cert

/-- The registers one iteration changes. -/
abbrev qiAll : List Reg := [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r10, .r12, .rbx]
/-- The registers of each segment. -/
abbrev qiA : List Reg := [.rax, .rcx, .rdi, .r8, .r10, .r12]
abbrev qiB : List Reg := [.rax, .rcx, .rdx, .rsi, .rdi]
abbrev qiC : List Reg := [.rax, .rcx, .rdx, .rbx]

theorem QiS.done {v v' : PState} {rs : List Reg} (h : QiS v v' rs) (hd : v.g.done = none) :
    v'.g.done = none := by rw [h.2.1]; exact hd

theorem QiS.code {W : World} {b : Word} {v v' : PState} {rs : List Reg} (h : QiS v v' rs)
    (hC : QiCode W b v.m.memory) : QiCode W b v'.m.memory := by rw [h.1]; exact hC

theorem QiS.trans {v1 v2 v3 : PState} {rs rs' : List Reg} (h1 : QiS v1 v2 rs) (h2 : QiS v2 v3 rs') :
    QiS v1 v3 (rs ++ rs') :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, fun r hr => by
    simp only [List.mem_append, not_or] at hr
    exact (h2.2.2.2 r hr.2).trans (h1.2.2.2 r hr.1)⟩

theorem QiS.mono {v v' : PState} {rs rs' : List Reg} (h : QiS v v' rs) (hs : ∀ r ∈ rs, r ∈ rs') :
    QiS v v' rs' := ⟨h.1, h.2.1, h.2.2.1, fun r hr => h.2.2.2 r fun h' => hr (hs r h')⟩

theorem QiS.refl (v : PState) (rs : List Reg) : QiS v v rs := ⟨rfl, rfl, rfl, fun _ _ => rfl⟩

variable {W : World} {b : Word} {Q : PState → Prop} {v : PState}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem qi_segA (hd : v.g.done = none) (hC : QiCode W b v.m.memory) (hrip : v.m.core.rip = b + 0x50c0#64)
    (hr14 : v.m.core.read .r14 = 0xffffffffffffffff#64) {nm : Word} {c : Byte} (hs : QSafe c)
    (hnm : loadN v.m.memory (v.m.core.read .rbp + 0xffffffffffffff90#64) 8 = some nm)
    (hc : loadN v.m.memory (nm + v.m.core.read .rbx) 1 = some (bw c))
    (h5c : loadN v.m.memory (v.m.core.read .rbp + 0xffffffffffffffa4#64) 4 = some 2#64)
    (h5f : loadN v.m.memory (v.m.core.read .rbp + 0xffffffffffffffa1#64) 1 = some 1#64)
    (h78 : loadN v.m.memory (v.m.core.read .rbp + 0xffffffffffffff88#64) 8 = some 1#64)
    (k : ∀ v' : PState, QiS v v' qiA → v'.m.core.rip = b + 0x510b#64 →
      (v'.m.core.read .r10).setWidth 8 = 1#8 → (v'.m.core.read .r12).setWidth 8 = 0#8 →
      (v'.m.core.read .r8).setWidth 8 = 0#8 → v'.m.core.read .rcx = nm + v.m.core.read .rbx → MustQ W Q v') :
    MustQ W Q v := by
  refine qi_50c0 hd hC hrip hr14 fun v1 S1 r1 => ?_
  refine qi_50cd (S1.done hd) (S1.code hC) r1 hs (by rw [S1.1, S1.2.2.2 .rbp (by decide)]; exact hnm)
    (by rw [S1.1, S1.2.2.2 .rbx (by decide)]; exact hc) fun v2 S2 r2 _ h10 => ?_
  have S12 := S1.trans S2
  refine qi_50d9 (S12.done hd) (S12.code hC) r2 h10 fun v3 S3 r3 => ?_
  have S13 := S12.trans S3
  refine qi_50e2 (S13.done hd) (S13.code hC) r3 (by rw [S13.1, S13.2.2.2 .rbp (by decide)]; exact h5c)
    (by rw [S13.1, S13.2.2.2 .rbp (by decide)]; exact hnm)
    (by rw [S13.1, S13.2.2.2 .rbp (by decide)]; exact h5f) fun v4 S4 r4 hax4 hdi4 => ?_
  have S14 := S13.trans S4
  refine qi_50f0 (S14.done hd) (S14.code hC) r4 (by rw [S14.1, S14.2.2.2 .rbp (by decide)]; exact h78)
    hax4 fun v5 S5 r5 hax5 hcx5 hr85 hfl5 => ?_
  have S15 := S14.trans S5
  refine qi_5102 (S15.done hd) (S15.code hC) r5 hfl5 hax5 fun v6 S6 r6 hr126 => ?_
  have S16 := S15.trans S6
  refine k v6 (S16.mono (by decide)) r6 ?_ hr126 ?_ ?_
  · rw [S6.2.2.2 .r10 (by decide), S5.2.2.2 .r10 (by decide), S4.2.2.2 .r10 (by decide),
      S3.2.2.2 .r10 (by decide)]; exact h10
  · rw [S6.2.2.2 .r8 (by decide)]; exact hr85
  · rw [S6.2.2.2 .rcx (by decide), hcx5, hdi4, S4.2.2.2 .rbx (by decide), S13.2.2.2 .rbx (by decide)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem qi_segB (hd : v.g.done = none) (hC : QiCode W b v.m.memory) (hrip : v.m.core.rip = b + 0x510b#64)
    {c : Byte} (hs : QSafe c) (hc : loadN v.m.memory (v.m.core.read .rcx) 1 = some (bw c))
    (hj : c.toNat ≤ 63 → loadN v.m.memory (b + BitVec.ofNat 64 (0x7f74 + 4 * c.toNat)) 4 = some qiJ)
    (k : ∀ v' : PState, QiS v v' qiB → v'.m.core.rip = b + 0x5165#64 → v'.m.core.read .rsi = bw c →
      MustQ W Q v') : MustQ W Q v := by
  refine qi_510b hd hC hrip hs hc (fun v1 S1 hl r1 hsi => ?_) (fun v1 S1 hl r1 hsi => ?_)
  · refine qi_5118 (S1.done hd) (S1.code hC) r1 hs hsi fun v2 S2 r2 => ?_
    have S12 := S1.trans S2
    refine qi_5121 (S12.done hd) (S12.code hC) r2 hs hl (by rw [S2.2.2.2 .rsi (by decide)]; exact hsi)
      fun v3 S3 r3 => ?_
    have S13 := S12.trans S3
    refine qi_512b (S13.done hd) (S13.code hC) r3
      (by rw [S3.2.2.2 .rsi (by decide), S2.2.2.2 .rsi (by decide)]; exact hsi)
      (by rw [S13.1]; exact hj hl) fun v4 S4 r4 => ?_
    refine k v4 ((S13.trans S4).mono (by decide)) r4 ?_
    rw [S4.2.2.2 .rsi (by decide), S3.2.2.2 .rsi (by decide), S2.2.2.2 .rsi (by decide)]; exact hsi
  · refine qi_5cc0 (S1.done hd) (S1.code hC) r1 hs hsi fun v2 S2 r2 => ?_
    have S12 := S1.trans S2
    refine qi_5cc6 (S12.done hd) (S12.code hC) r2 hs hl (by rw [S2.2.2.2 .rsi (by decide)]; exact hsi)
      fun v3 S3 r3 => ?_
    have S13 := S12.trans S3
    refine qi_5cd0 (S13.done hd) (S13.code hC) r3 hs hl
      (by rw [S3.2.2.2 .rsi (by decide), S2.2.2.2 .rsi (by decide)]; exact hsi) fun v4 S4 r4 => ?_
    refine k v4 ((S13.trans S4).mono (by decide)) r4 ?_
    rw [S4.2.2.2 .rsi (by decide), S3.2.2.2 .rsi (by decide), S2.2.2.2 .rsi (by decide)]; exact hsi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem qi_segC (hd : v.g.done = none) (hC : QiCode W b v.m.memory) (hrip : v.m.core.rip = b + 0x5165#64)
    {c : Byte} (hs : QSafe c) (hrsi : v.m.core.read .rsi = bw c)
    (hr8 : (v.m.core.read .r8).setWidth 8 = 0#8) (hr12 : (v.m.core.read .r12).setWidth 8 = 0#8)
    {A : Word} (hA : A ≠ 0#64)
    (h5d : loadN v.m.memory (v.m.core.read .rbp + 0xffffffffffffffa3#64) 1 = some 1#64)
    (h80 : loadN v.m.memory (v.m.core.read .rbp + 0xffffffffffffff80#64) 8 = some A)
    (hq : loadN v.m.memory (A + BitVec.ofNat 64 (4 * (c.toNat / 32))) 4 = some (qiQ c))
    (h5c : loadN v.m.memory (v.m.core.read .rbp + 0xffffffffffffffa4#64) 4 = some 2#64)
    (h5e : loadN v.m.memory (v.m.core.read .rbp + 0xffffffffffffffa2#64) 1 = some 0#64)
    (k : ∀ v' : PState, QiS v v' qiC → v'.m.core.rip = b + 0x5207#64 →
      v'.m.core.read .rbx = v.m.core.read .rbx + 1#64 → v'.m.core.read .rsi = bw c → MustQ W Q v') :
    MustQ W Q v := by
  refine qi_5165 hd hC hrip h5d hr8 fun v1 S1 r1 hfl1 => ?_
  refine qi_516b (S1.done hd) (S1.code hC) r1 hfl1 fun v2 S2 r2 => ?_
  have S12 := S1.trans S2
  refine qi_5171 (S12.done hd) (S12.code hC) r2 (by rw [S12.1, S12.2.2.2 .rbp (by decide)]; exact h80) hA
    fun v3 S3 r3 _ hcx3 => ?_
  have S13 := S12.trans S3
  have hsi3 : v3.m.core.read .rsi = bw c := by rw [S13.2.2.2 .rsi (by decide)]; exact hrsi
  refine qi_5180 (S13.done hd) (S13.code hC) r3 hsi3 fun v4 S4 r4 hdx4 => ?_
  have S14 := S13.trans S4
  refine qi_5185 (A := A) (S14.done hd) (S14.code hC) r4 hs (by rw [S4.2.2.2 .rsi (by decide)]; exact hsi3)
    (by rw [S4.2.2.2 .rcx (by decide)]; exact hcx3) hdx4 (by rw [S14.1]; exact hq) fun v5 S5 r5 => ?_
  have S15 := S14.trans S5
  refine qi_5248 (S15.done hd) (S15.code hC) r5 (by rw [S15.1, S15.2.2.2 .rbp (by decide)]; exact h5c)
    (by rw [S15.2.2.2 .r12 (by decide)]; exact hr12) fun v6 S6 r6 => ?_
  have S16 := S15.trans S6
  refine qi_5258 (S16.done hd) (S16.code hC) r6 (by rw [S16.1, S16.2.2.2 .rbp (by decide)]; exact h5e)
    fun v7 S7 r7 hax7 hbx7 => ?_
  have S17 := S16.trans S7
  refine qi_5262 (S17.done hd) (S17.code hC) r7 hax7 fun v8 S8 r8 => ?_
  refine k v8 ((S17.trans S8).mono (by decide)) r8 ?_ ?_
  · rw [S8.2.2.2 .rbx (by decide), hbx7, S16.2.2.2 .rbx (by decide)]
  · rw [S8.2.2.2 .rsi (by decide), S7.2.2.2 .rsi (by decide), S6.2.2.2 .rsi (by decide),
      S5.2.2.2 .rsi (by decide), S4.2.2.2 .rsi (by decide)]; exact hsi3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem qi_segD {i : Nat} (hd : v.g.done = none) (hC : QiCode W b v.m.memory)
    (hC' : ∀ y, QiCode W b (storeMem v.m.memory (v.m.core.read .r9 + BitVec.ofNat 64 i) 1 y))
    (hrip : v.m.core.rip = b + 0x5207#64)
    {c : Byte} (hrsi : v.m.core.read .rsi = bw c) (hi : i < 256) {x : Word}
    (hlen : loadN v.m.memory (v.m.core.read .rbp + 0xffffffffffffffa8#64) 8 = some (BitVec.ofNat 64 i))
    (hpend : loadN v.m.memory (v.m.core.read .rbp + 0xffffffffffffff98#64) 1 = some x)
    (hr11 : v.m.core.read .r11 = 256#64)
    (hw : v.m.memory.Permitted .write (v.m.core.read .r9 + BitVec.ofNat 64 i).toNat 1)
    (hw1 : v.m.memory.Permitted .write (v.m.core.read .rbp + 0xffffffffffffffa8#64).toNat 8)
    (hw2 : v.m.memory.Permitted .write (v.m.core.read .rbp + 0xffffffffffffff98#64).toNat 1)
    (hd1 : (v.m.core.read .r9 + BitVec.ofNat 64 i).toNat + 1 ≤ (v.m.core.read .rbp + 0xffffffffffffffa8#64).toNat ∨
      (v.m.core.read .rbp + 0xffffffffffffffa8#64).toNat + 8 ≤ (v.m.core.read .r9 + BitVec.ofNat 64 i).toNat)
    (hd2 : (v.m.core.read .r9 + BitVec.ofNat 64 i).toNat + 1 ≤ (v.m.core.read .rbp + 0xffffffffffffff98#64).toNat ∨
      (v.m.core.read .rbp + 0xffffffffffffff98#64).toNat + 1 ≤ (v.m.core.read .r9 + BitVec.ofNat 64 i).toNat)
    (k : ∀ v' : PState, (∃ y, v'.m.memory = storeMem (storeMem (storeMem v.m.memory
        (v.m.core.read .r9 + BitVec.ofNat 64 i) 1 (bw c)) (v.m.core.read .rbp + 0xffffffffffffffa8#64) 8
        (BitVec.ofNat 64 i + 1#64)) (v.m.core.read .rbp + 0xffffffffffffff98#64) 1 y) →
      v'.g = v.g → v'.m.core.fsBase = v.m.core.fsBase →
      (∀ r, r ∉ [Reg.rax, Reg.rdi] → v'.m.core.read r = v.m.core.read r) →
      v'.m.core.rip = b + 0x50c0#64 → MustQ W Q v') : MustQ W Q v := by
  refine qi_5207 hd hC hrip hi hlen hr11 fun v1 S1 r1 hax1 => ?_
  have e9 : v1.m.core.read .r9 + v1.m.core.read .rax = v.m.core.read .r9 + BitVec.ofNat 64 i := by
    rw [hax1, S1.2.2.2 .r9 (by decide)]
  refine qi_5210 (S1.done hd) (S1.code hC) r1 (c := c) (by rw [S1.2.2.2 .rsi (by decide)]; exact hrsi)
    (by rw [e9, S1.1]; exact hw) fun v2 hm2 hg2 hf2 hr2 r2 => ?_
  rw [e9, S1.1] at hm2
  have rb : v2.m.core.read .rbp = v.m.core.read .rbp := by rw [hr2, S1.2.2.2 .rbp (by decide)]
  refine qi_5214 (by rw [hg2, S1.2.1]; exact hd) (by rw [hm2]; exact hC' _) r2 (x := x)
    (by rw [hm2, rb, loadN_storeMem_ne hd2]; exact hpend)
    (by rw [hm2, rb, loadN_storeMem_ne hd1]; exact hlen)
    (by rw [hm2, rb]; exact hw1) (by rw [hm2, rb]; exact hw2) fun v3 hm3 hg3 hf3 hr3 r3 => ?_
  refine k v3 ?_ (hg3.trans (hg2.trans S1.2.1)) (hf3.trans (hf2.trans S1.2.2.1)) ?_ r3
  · rw [hm2, rb] at hm3; exact hm3
  · intro r hr
    rw [hr3 r hr, hr2, S1.2.2.2 r (fun h => hr (by simp at h ⊢; exact Or.inl h))]

end Silmaril.Elf.Link.Dyn.Sha256sum
