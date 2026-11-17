module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.TailOpts

/-! # GNU `sha256sum`: `main` with no operand, the operand `"-"` (`0x2ae3`–`0x2b81`)

`optind == argc`: `main` stores `"-"` in `argv[argc]` (the vector's terminating slot) and takes
it as the only operand; the loop's frame slots are set (`end = &argv[argc+1]`, the `missing`
byte's address, the `ok` byte) and `digest_file ("-", bin_result, &missing)` is called at
`0x2b81`. One lemma per block (`CertMainAll`).
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
/-- Block `0x2ae3`: `optind == argc` (= 1): `rax = 1`, `rcx = &argv[1]`, to `0x2af9`. -/
theorem step2ae3 {W : World} {b : Word} (I : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64)
    {Q : PState → Prop} {u : PState} (hd : u.g.done = none) (hMA : ShaMainAll b u.m.memory)
    (hrip : u.m.core.rip = b + 0x2ae3#64) {A : Word}
    (hgot : loadN u.m.memory (u.m.core.rip + 0x74e5#64) 8 = some A)
    (hopt : loadN u.m.memory A 4 = some 1#64)
    (hr12 : BitVec.setWidth 32 (u.m.core.read .r12) = 1#32)
    (k : ∀ w, w.m.core.rip = b + 0x2af9#64 → w.m.memory = u.m.memory → w.g = u.g →
      (∀ r, r ≠ .rax → r ≠ .rcx → w.m.core.read r = u.m.core.read r) → w.m.core.read .rax = 1#64 →
      w.m.core.read .rcx = u.m.core.read .rbx + 8#64 → w.m.core.fsBase = u.m.core.fsBase → MustQ W Q w) :
    MustQ W Q u := by
  obtain ⟨-, l1, l2, -⟩ := mainAll_lens
  have e12 : (BitVec.setWidth 32 (u.m.core.read .r12)).signExtend 64 = 1#64 := by rw [hr12]; decide
  refine must_piece I hb hd (cb := 0x2952) (by omega) hMA.ld1 hMA.ro1 blk2ae3 blk2ae3_ok
    (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp
  rotate_left
  · rename_i v0 h0 v1 h1
    rw [hgot] at h0; cases h0; rw [hopt] at h1; cases h1; rw [hr12]
    exact ⟨false, by decide +kernel⟩
  · rename_i v0 h0
    rw [hgot] at h0; cases h0; exact ⟨_, hopt⟩
  · exact ⟨_, hgot⟩
  rename_i v0 h0 v1 h1 bv hbv
  refine k _ ?_ (Eq.refl _) rfl (fun r h1 h2 => state_read_other (by simp [blk2ae3, h1, h2])) ?_ ?_ rfl
  · rw [hgot] at h0; cases h0; rw [hopt] at h1; cases h1; rw [hr12] at hbv
    have hb1 : bv = false := by revert bv; decide +kernel
    subst hb1
    blk_simp [blk2ae3, hrip]
    rw [ite_f (by decide)]
  · rw [hgot] at h0; cases h0; rw [hopt] at h1; cases h1
    blk_simp [blk2ae3]
    decide +kernel
  · blk_simp [blk2ae3]
    rw [e12]
    exact congrArg (_ + ·) (by decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
/-- Block `0x2af9`: `argv[argc] = "-"`, `rcx += 8`, `rdi = "-"`, to `0x2b08`. -/
theorem step2af9 {W : World} {b : Word} (I : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64)
    {Q : PState → Prop} {u : PState} (hd : u.g.done = none) (hMA : ShaMainAll b u.m.memory)
    (hrip : u.m.core.rip = b + 0x2af9#64)
    (hw : u.m.memory.Permitted .write (u.m.core.read .rcx + 0#64).toNat 8)
    (k : ∀ w, w.m.core.rip = b + 0x2b08#64 →
      w.m.memory = storeMem u.m.memory (u.m.core.read .rcx + 0#64) 8 (u.m.core.rip + 0x4675#64) → w.g = u.g →
      (∀ r, r ≠ .rcx → r ≠ .rdi → w.m.core.read r = u.m.core.read r) →
      w.m.core.read .rcx = u.m.core.read .rcx + 8#64 → w.m.core.read .rdi = u.m.core.rip + 0x4675#64 →
      w.m.core.fsBase = u.m.core.fsBase → MustQ W Q w) :
    MustQ W Q u := by
  obtain ⟨-, l1, l2, -⟩ := mainAll_lens
  refine must_piece I hb hd (cb := 0x2952) (by omega) hMA.ld1 hMA.ro1 blk2af9 blk2af9_ok
    (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp
  rotate_left
  · exact hw
  refine k _ ?_ (Eq.refl _) rfl (fun r h1 h2 => state_read_other (by simp [blk2af9, h1, h2])) ?_ ?_ rfl
  · blk_simp [blk2af9, hrip]
  · blk_simp [blk2af9]
  · blk_simp [blk2af9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
/-- Block `0x2b08`: `r8 = &argv[optind]` below the end: to `0x2b15`. -/
theorem step2b08 {W : World} {b : Word} (I : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64)
    {Q : PState → Prop} {u : PState} (hd : u.g.done = none) (hMA : ShaMainAll b u.m.memory)
    (hrip : u.m.core.rip = b + 0x2b08#64) (hrax : u.m.core.read .rax = 1#64)
    (hlt : (u.m.core.read .rbx + 8#64).ult (u.m.core.read .rcx) = true)
    (k : ∀ w, w.m.core.rip = b + 0x2b15#64 → w.m.memory = u.m.memory → w.g = u.g →
      (∀ r, r ≠ .r8 → w.m.core.read r = u.m.core.read r) → w.m.core.read .r8 = u.m.core.read .rbx + 8#64 →
      w.m.core.fsBase = u.m.core.fsBase → MustQ W Q w) :
    MustQ W Q u := by
  obtain ⟨-, l1, l2, -⟩ := mainAll_lens
  have e8 : u.m.core.read .rax <<< 3 = 8#64 := by rw [hrax]; decide
  refine must_piece I hb hd (cb := 0x2952) (by omega) hMA.ld1 hMA.ro1 blk2b08 blk2b08_ok
    (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp
  rotate_left
  · exact eval_some (defined_alu _ _ _ _) _
  rename_i bv hbv
  refine k _ ?_ (Eq.refl _) rfl (fun r h1 => state_read_other (by simp [blk2b08, h1])) ?_ rfl
  · simp only [Silmaril.X86.Ext.AluOp.flagsN, eval_ae_sub, e8, BitVec.setWidth_eq, hlt, Bool.not_true,
      Option.some.injEq] at hbv
    subst hbv
    blk_simp [blk2b08, hrip]
    rw [ite_f (by decide)]
  · blk_simp [blk2b08]
    rw [e8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
/-- Block `0x2b15`: `r12 = argv[optind]`, saved at `rbp-0x100`; `--check` off: to `0x2b2c`. -/
theorem step2b15 {W : World} {b : Word} (I : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64)
    {Q : PState → Prop} {u : PState} (hd : u.g.done = none) (hMA : ShaMainAll b u.m.memory)
    (hrip : u.m.core.rip = b + 0x2b15#64) {nm : Word}
    (hn : loadN u.m.memory (u.m.core.read .r8) 8 = some nm)
    (hc : loadN u.m.memory (u.m.core.read .rbp + 0xffffffffffffff20#64) 1 = some 0#64)
    (hw : u.m.memory.Permitted .write (u.m.core.read .rbp + 0xffffffffffffff00#64).toNat 8)
    (k : ∀ w, w.m.core.rip = b + 0x2b2c#64 →
      w.m.memory = storeMem u.m.memory (u.m.core.read .rbp + 0xffffffffffffff00#64) 8 nm → w.g = u.g →
      (∀ r, r ≠ .r12 → w.m.core.read r = u.m.core.read r) → w.m.core.read .r12 = nm →
      w.m.core.fsBase = u.m.core.fsBase → MustQ W Q w) :
    MustQ W Q u := by
  obtain ⟨-, l1, l2, -⟩ := mainAll_lens
  refine must_piece I hb hd (cb := 0x2952) (by omega) hMA.ld1 hMA.ro1 blk2b15 blk2b15_ok
    (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp
  rotate_left
  · rename_i v0 h0 v1 h1
    rw [hc] at h1; cases h1
    exact ⟨false, by decide +kernel⟩
  · exact hw
  · exact ⟨_, hc⟩
  · exact ⟨_, hn⟩
  rename_i v0 h0 v1 h1 bv hbv
  rw [hn] at h0; cases h0
  refine k _ ?_ (Eq.refl _) rfl (fun r h1 => state_read_other (by simp [blk2b15, h1])) ?_ rfl
  · rw [hc] at h1; cases h1
    have hb1 : bv = false := by revert bv; decide +kernel
    subst hb1
    blk_simp [blk2b15, hrip]
    rw [ite_f (by decide)]
  · blk_simp [blk2b15]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
/-- Block `0x2b2c`: the loop's frame slots (`end`, `&missing`, `ok`), `rbx = bin_result`,
`r14 = "%02x"`, `r15 = &argv[i]`, to `0x2b74`. -/
theorem step2b2c {W : World} {b : Word} (I : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64)
    {Q : PState → Prop} {u : PState} (hd : u.g.done = none) (hMA : ShaMainAll b u.m.memory)
    (hrip : u.m.core.rip = b + 0x2b2c#64)
    (hw1 : u.m.memory.Permitted .write (u.m.core.read .rbp + 0xffffffffffffff18#64).toNat 8)
    (hw2 : (storeMem u.m.memory (u.m.core.read .rbp + 0xffffffffffffff18#64) 8 (u.m.core.read .rcx)).Permitted
      .write (u.m.core.read .rbp + 0xffffffffffffff20#64).toNat 8)
    (hw3 : (storeMem (storeMem u.m.memory (u.m.core.read .rbp + 0xffffffffffffff18#64) 8 (u.m.core.read .rcx))
      (u.m.core.read .rbp + 0xffffffffffffff20#64) 8 (u.m.core.read .rbp + 0xffffffffffffff58#64)).Permitted
      .write (u.m.core.read .rbp + 0xffffffffffffff28#64).toNat 1)
    (k : ∀ w, w.m.core.rip = b + 0x2b74#64 →
      w.m.memory = storeMem (storeMem (storeMem u.m.memory (u.m.core.read .rbp + 0xffffffffffffff18#64) 8
        (u.m.core.read .rcx)) (u.m.core.read .rbp + 0xffffffffffffff20#64) 8
        (u.m.core.read .rbp + 0xffffffffffffff58#64)) (u.m.core.read .rbp + 0xffffffffffffff28#64) 1
        (((u.m.core.read .rdx).setWidth 8).setWidth 64) → w.g = u.g →
      (∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .r14 → r ≠ .r15 → w.m.core.read r = u.m.core.read r) →
      w.m.core.read .rbx = u.m.core.read .rbp + 0xffffffffffffffa0#64 →
      w.m.core.read .r14 = u.m.core.rip + 0x470c#64 → w.m.core.read .r15 = u.m.core.read .r8 →
      w.m.core.fsBase = u.m.core.fsBase → MustQ W Q w) :
    MustQ W Q u := by
  obtain ⟨-, l1, l2, -⟩ := mainAll_lens
  refine must_piece I hb hd (cb := 0x2b2c) (by omega) hMA.ld2 hMA.ro2 blk2b2c blk2b2c_ok
    (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp
  rotate_left
  · exact hw3
  · exact hw2
  · exact hw1
  refine k _ ?_ (Eq.refl _) rfl (fun r h1 h2 h3 h4 => state_read_other (by simp [blk2b2c, h1, h2, h3, h4]))
    ?_ ?_ ?_ rfl
  · blk_simp [blk2b2c, hrip]
  · blk_simp [blk2b2c]
  · blk_simp [blk2b2c]
  · blk_simp [blk2b2c]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
/-- Block `0x2b74`: the arguments of `digest_file (r12, rbx, [rbp-0xe0])`, to the call at `0x2b81`. -/
theorem step2b74 {W : World} {b : Word} (I : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64)
    {Q : PState → Prop} {u : PState} (hd : u.g.done = none) (hMA : ShaMainAll b u.m.memory)
    (hrip : u.m.core.rip = b + 0x2b74#64) {dx : Word}
    (hdx : loadN u.m.memory (u.m.core.read .rbp + 0xffffffffffffff20#64) 8 = some dx)
    (k : ∀ w, w.m.core.rip = b + 0x2b81#64 → w.m.memory = u.m.memory → w.g = u.g →
      (∀ r, r ≠ .rdx → r ≠ .rsi → r ≠ .rdi → w.m.core.read r = u.m.core.read r) →
      w.m.core.read .rdx = dx → w.m.core.read .rsi = u.m.core.read .rbx →
      w.m.core.read .rdi = u.m.core.read .r12 → w.m.core.fsBase = u.m.core.fsBase → MustQ W Q w) :
    MustQ W Q u := by
  obtain ⟨-, l1, l2, -⟩ := mainAll_lens
  refine must_piece I hb hd (cb := 0x2b2c) (by omega) hMA.ld2 hMA.ro2 blk2b74 blk2b74_ok
    (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp
  rotate_left
  · exact ⟨_, hdx⟩
  rename_i v0 h0
  refine k _ ?_ (Eq.refl _) rfl (fun r h1 h2 h3 => state_read_other (by simp [blk2b74, h1, h2, h3]))
    ?_ ?_ ?_ rfl
  · blk_simp [blk2b74, hrip]
  · rw [hdx] at h0; cases h0; blk_simp [blk2b74]
  · blk_simp [blk2b74]
  · blk_simp [blk2b74]

end Silmaril.Elf.Link.Dyn.Sha256sum
