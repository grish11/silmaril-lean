module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.TailRun4

/-! # GNU `sha256sum FILE…`: the blocks of `main`'s operand loop not on the stdin path

* `step2ae3n`: `optind != argc` (there are operands): to `0x2b08`, `rcx = &argv[argc]`;
* `step2b57c`: the loop's head with an operand left: to `0x2b6b`;
* `step2b6b`: `ok` stored back at `rbp-0xd8`, `r12 = argv[i]`: to `0x2b74`.

One lemma per block of `CertMainAll` (`mainAll1Text`/`mainAll2Text`).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Cert

theorem eval_ne_sub32 (x y : BitVec 32) :
    Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.subFlagsN x y) .ne = some (!decide (x = y)) := by
  simp only [Silmaril.X86.Ext.subFlagsN, Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.kNot,
    Silmaril.X86.Ext.isZeroN, Option.map_some]
  by_cases h : x = y
  · subst h; simp
  · have : x - y ≠ 0#32 := fun he => h (by bv_omega)
    simp [h, this]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
/-- Block `0x2ae3`: `optind != argc` (`optind = 1`, `argc = n`, `n ≠ 1`): `rax = 1`,
`rcx = &argv[argc]`, to `0x2b08`. -/
theorem step2ae3n {W : World} {b : Word} (I : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64)
    {Q : PState → Prop} {u : PState} (hd : u.g.done = none) (hMA : ShaMainAll b u.m.memory)
    (hrip : u.m.core.rip = b + 0x2ae3#64) {A : Word}
    (hgot : loadN u.m.memory (u.m.core.rip + 0x74e5#64) 8 = some A)
    (hopt : loadN u.m.memory A 4 = some 1#64) {n : BitVec 32}
    (hr12 : BitVec.setWidth 32 (u.m.core.read .r12) = n) (hn : n ≠ 1#32)
    (k : ∀ w, w.m.core.rip = b + 0x2b08#64 → w.m.memory = u.m.memory → w.g = u.g →
      (∀ r, r ≠ .rax → r ≠ .rcx → w.m.core.read r = u.m.core.read r) → w.m.core.read .rax = 1#64 →
      w.m.core.read .rcx = u.m.core.read .rbx + (n.signExtend 64 <<< 3) →
      w.m.core.fsBase = u.m.core.fsBase → MustQ W Q w) :
    MustQ W Q u := by
  obtain ⟨-, l1, l2, -⟩ := mainAll_lens
  refine must_piece I hb hd (cb := 0x2952) (by omega) hMA.ld1 hMA.ro1 blk2ae3 blk2ae3_ok
    (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp
  rotate_left
  · rename_i v0 h0 v1 h1
    rw [hgot] at h0; cases h0; rw [hopt] at h1; cases h1
    exact ⟨_, by simp only [Silmaril.X86.Ext.AluOp.flagsN]; exact eval_ne_sub32 _ _⟩
  · rename_i v0 h0
    rw [hgot] at h0; cases h0; exact ⟨_, hopt⟩
  · exact ⟨_, hgot⟩
  rename_i v0 h0 v1 h1 bv hbv
  refine k _ ?_ (Eq.refl _) rfl (fun r h1 h2 => state_read_other (by simp [blk2ae3, h1, h2])) ?_ ?_ rfl
  · rw [hgot] at h0; cases h0; rw [hopt] at h1; cases h1
    simp only [Silmaril.X86.Ext.AluOp.flagsN] at hbv
    rw [eval_ne_sub32, Option.some.injEq] at hbv
    subst hbv
    have hcond : (!decide (BitVec.setWidth 32 (BitVec.signExtend 64 (BitVec.setWidth 32 1#64)) =
        BitVec.setWidth 32 (u.m.core.read Reg.r12))) = true := by
      rw [hr12]; simp only [Bool.not_eq_true', decide_eq_false_iff_not]
      intro h; exact hn (h.symm.trans (by decide))
    blk_simp [blk2ae3, hrip]
    rw [ite_t (by rw [hcond]; decide)]
  · rw [hgot] at h0; cases h0; rw [hopt] at h1; cases h1
    blk_simp [blk2ae3]
    decide +kernel
  · blk_simp [blk2ae3]
    rw [hr12]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
/-- Block `0x2b57` with an operand left: to `0x2b6b`. -/
theorem step2b57c {W : World} {b : Word} (I : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64)
    {Q : PState → Prop} {u : PState} (hd : u.g.done = none) (hMA : ShaMainAll b u.m.memory)
    (hrip : u.m.core.rip = b + 0x2b57#64) {endp : Word}
    (hend : loadN u.m.memory (u.m.core.read .rbp + 0xffffffffffffff18#64) 8 = some endp)
    (hc : (u.m.core.read .r15 + 8#64).ult endp = true)
    (k : ∀ w, w.m.core.rip = b + 0x2b6b#64 → w.m.memory = u.m.memory → w.g = u.g →
      (∀ r, r ≠ .rdi → r ≠ .r15 → w.m.core.read r = u.m.core.read r) →
      w.m.core.read .r15 = u.m.core.read .r15 + 8#64 → w.m.core.fsBase = u.m.core.fsBase → MustQ W Q w) :
    MustQ W Q u := by
  obtain ⟨-, -, l2, -⟩ := mainAll_lens
  refine must_piece I hb hd (cb := 0x2b2c) (by omega) hMA.ld2 hMA.ro2 blk2b57 blk2b57_ok
    (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp
  rotate_left
  · exact eval_some (defined_alu _ _ _ _) _
  · exact ⟨_, hend⟩
  rename_i v0 h0 bv hbv
  rw [hend] at h0; cases h0
  simp only [Silmaril.X86.Ext.AluOp.flagsN, BitVec.setWidth_eq, eval_ae_sub, Option.some.injEq] at hbv
  subst hbv
  refine k _ ?_ (Eq.refl _) rfl (fun r h1 h2 => state_read_other (by simp [blk2b57, h1, h2])) ?_ rfl
  · blk_simp [blk2b57, hrip, hc]; simp
  · blk_simp [blk2b57]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
/-- Block `0x2b6b`: `ok` (`al`) stored at `rbp-0xd8`, `r12 = argv[i]` (`[r15]`): to `0x2b74`. -/
theorem step2b6b {W : World} {b : Word} (I : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64)
    {Q : PState → Prop} {u : PState} (hd : u.g.done = none) (hMA : ShaMainAll b u.m.memory)
    (hrip : u.m.core.rip = b + 0x2b6b#64)
    (hw : u.m.memory.Permitted .write (u.m.core.read .rbp + 0xffffffffffffff28#64).toNat 1) {nm : Word}
    (hn : loadN (storeMem u.m.memory (u.m.core.read .rbp + 0xffffffffffffff28#64) 1
      (((u.m.core.read .rax).setWidth 8).setWidth 64)) (u.m.core.read .r15) 8 = some nm)
    (k : ∀ w, w.m.core.rip = b + 0x2b74#64 →
      w.m.memory = storeMem u.m.memory (u.m.core.read .rbp + 0xffffffffffffff28#64) 1
        (((u.m.core.read .rax).setWidth 8).setWidth 64) → w.g = u.g →
      (∀ r, r ≠ .r12 → w.m.core.read r = u.m.core.read r) → w.m.core.read .r12 = nm →
      w.m.core.fsBase = u.m.core.fsBase → MustQ W Q w) :
    MustQ W Q u := by
  obtain ⟨-, -, l2, -⟩ := mainAll_lens
  refine must_piece I hb hd (cb := 0x2b2c) (by omega) hMA.ld2 hMA.ro2 blk2b6b blk2b6b_ok
    (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp
  rotate_left
  · exact ⟨_, hn⟩
  · exact hw
  rename_i v0 h0
  rw [hn] at h0; cases h0
  refine k _ ?_ (Eq.refl _) rfl (fun r h1 => state_read_other (by simp [blk2b6b, h1])) ?_ rfl
  · blk_simp [blk2b6b, hrip]
  · blk_simp [blk2b6b]

end Silmaril.Elf.Link.Dyn.Sha256sum
