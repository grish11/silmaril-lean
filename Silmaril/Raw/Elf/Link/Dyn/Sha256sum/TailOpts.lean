module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.TailBase

/-! # GNU `sha256sum`: `main` after option parsing, with no operand (`0x29fd`–`0x2ae3`)

`binary` unset (`-1`): `digest_hex_bytes = 64` and `digest_bin_bytes`… are stored (`.bss`
`0xa168`, `0xa178`); the delimiter is `'\n'`, `
are clear: control reaches `0x2ae3` with `edx = 1` (the `ok` flag) and `eax = 0`.

One lemma per block (`stepXXXX`, from `CertMainAll`'s certificates) or per instruction the lifter
leaves out (`gap2abf`, `gap2ad7`, the 8-bit memory ALU forms, stepped on `mainCListing`). Each
step's continuation is discharged before the block's values are made concrete (closed values in
the block's environment make the kernel's checks expensive).
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

/-- The two `.bss` words `main` stores once the options are parsed. -/
def optMem (m : Memory) (b : Word) : Memory :=
  storeMem (storeMem m (b + 0xa168#64) 8 0x42#64) (b + 0xa178#64) 8 0x40#64

theorem optMem_keep {b : Word} (hb : b.toNat + 0xa188 < 2 ^ 64) (m : Memory) :
    Keeps (fun x => ImgW b x ∨ ¬ ShaImg b x) m (optMem m b) := by
  have e1 : (b + 0xa168#64).toNat = b.toNat + 0xa168 := addr_toNat (v := 0xa168) (by omega)
  have e2 : (b + 0xa178#64).toNat = b.toNat + 0xa178 := addr_toNat (v := 0xa178) (by omega)
  refine (storeMem_keeps fun x hx => ?_).trans (storeMem_keeps fun x hx => ?_)
  · rw [e1]; rcases hx with ⟨⟨h1, h2⟩, h3⟩ | h <;> [omega; (by_contra hc; exact h ⟨by omega, by omega⟩)]
  · rw [e2]; rcases hx with ⟨⟨h1, h2⟩, h3⟩ | h <;> [omega; (by_contra hc; exact h ⟨by omega, by omega⟩)]

/-- A step's continuation: control at `ip`, memory `m`, the other registers kept. -/
abbrev StepK (W : World) (Q : PState → Prop) (u : PState) (ip : Word) (m : Memory) : Prop :=
  ∀ w, w.m.core.rip = ip → w.m.memory = m → w.g = u.g → (∀ r, w.m.core.read r = u.m.core.read r) →
    w.m.core.fsBase = u.m.core.fsBase → MustQ W Q w

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
/-- Block `0x2a29`: the delimiter is `'\\n'`: to `0x2c96`. -/
theorem step2a29 {W : World} {b : Word} (I : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64)
    {Q : PState → Prop} {u : PState} (hd : u.g.done = none) (hMA : ShaMainAll b u.m.memory)
    (hrip : u.m.core.rip = b + 0x2a29#64)
    (hl : loadN u.m.memory (u.m.core.rip + 0x75f3#64) 1 = some 0x0a#64)
    (k : StepK W Q u (b + 0x2c96#64) u.m.memory) : MustQ W Q u := by
  obtain ⟨-, l1, l2, -⟩ := mainAll_lens
  refine must_piece I hb hd (cb := 10578) (by omega) hMA.ld1 hMA.ro1 blk2a29 blk2a29_ok
    (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp
  rotate_left
  · rename_i v0 h0
    rw [hl] at h0
    cases h0
    exact ⟨true, by decide +kernel⟩
  · exact ⟨_, hl⟩
  rename_i v0 h0 bv hbv
  refine k _ ?_ (Eq.refl _) rfl (fun r => state_read_other (by simp [blk2a29])) rfl
  rw [hl] at h0
  cases h0
  have hb1 : bv = true := by revert bv; decide +kernel
  subst hb1
  blk_simp [blk2a29, hrip]
  rw [ite_t (by decide)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
/-- Block `0x2c96`: `--check` is off: to `0x2cb4`. -/
theorem step2c96 {W : World} {b : Word} (I : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64)
    {Q : PState → Prop} {u : PState} (hd : u.g.done = none) (hMA : ShaMainAll b u.m.memory)
    (hrip : u.m.core.rip = b + 0x2c96#64)
    (hl : loadN u.m.memory (u.m.core.read .rbp + 0xffffffffffffff20#64) 1 = some 0#64)
    (k : StepK W Q u (b + 0x2cb4#64) u.m.memory) : MustQ W Q u := by
  obtain ⟨-, l1, l2, -⟩ := mainAll_lens
  refine must_piece I hb hd (cb := 11052) (by omega) hMA.ld2 hMA.ro2 blk2c96 blk2c96_ok
    (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp
  rotate_left
  · rename_i v0 h0
    rw [hl] at h0
    cases h0
    exact ⟨true, by decide +kernel⟩
  · exact ⟨_, hl⟩
  rename_i v0 h0 bv hbv
  refine k _ ?_ (Eq.refl _) rfl (fun r => state_read_other (by simp [blk2c96])) rfl
  rw [hl] at h0
  cases h0
  have hb1 : bv = true := by revert bv; decide +kernel
  subst hb1
  blk_simp [blk2c96, hrip]
  rw [ite_t (by decide)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
/-- Block `0x2cb4`: `binary < 0`: back to `0x2a4f`. -/
theorem step2cb4 {W : World} {b : Word} (I : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64)
    {Q : PState → Prop} {u : PState} (hd : u.g.done = none) (hMA : ShaMainAll b u.m.memory)
    (hrip : u.m.core.rip = b + 0x2cb4#64)
    (hl : loadN u.m.memory (u.m.core.read .rbp + 0xffffffffffffff38#64) 4 = some 0xffffffff#64)
    (k : StepK W Q u (b + 0x2a4f#64) u.m.memory) : MustQ W Q u := by
  obtain ⟨-, l1, l2, -⟩ := mainAll_lens
  refine must_piece I hb hd (cb := 11052) (by omega) hMA.ld2 hMA.ro2 blk2cb4 blk2cb4_ok
    (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp
  rotate_left
  · rename_i v0 h0
    rw [hl] at h0
    cases h0
    exact ⟨true, by decide +kernel⟩
  · exact ⟨_, hl⟩
  rename_i v0 h0 bv hbv
  refine k _ ?_ (Eq.refl _) rfl (fun r => state_read_other (by simp [blk2cb4])) rfl
  rw [hl] at h0
  cases h0
  have hb1 : bv = true := by revert bv; decide +kernel
  subst hb1
  blk_simp [blk2cb4, hrip]
  rw [ite_t (by decide)]
  exact congrArg (b + ·) rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
/-- Block `0x2a4f`: flag `0xa171` clear: to `0x2a71`. -/
theorem step2a4f {W : World} {b : Word} (I : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64)
    {Q : PState → Prop} {u : PState} (hd : u.g.done = none) (hMA : ShaMainAll b u.m.memory)
    (hrip : u.m.core.rip = b + 0x2a4f#64)
    (hl : loadN u.m.memory (u.m.core.rip + 0x7722#64) 1 = some 0#64)
    (k : StepK W Q u (b + 0x2a71#64) u.m.memory) : MustQ W Q u := by
  obtain ⟨-, l1, l2, -⟩ := mainAll_lens
  refine must_piece I hb hd (cb := 10578) (by omega) hMA.ld1 hMA.ro1 blk2a4f blk2a4f_ok
    (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp
  rotate_left
  · rename_i v0 h0
    rw [hl] at h0
    cases h0
    exact ⟨true, by decide +kernel⟩
  · exact ⟨_, hl⟩
  rename_i v0 h0 bv hbv
  refine k _ ?_ (Eq.refl _) rfl (fun r => state_read_other (by simp [blk2a4f])) rfl
  rw [hl] at h0
  cases h0
  have hb1 : bv = true := by revert bv; decide +kernel
  subst hb1
  blk_simp [blk2a4f, hrip]
  rw [ite_t (by decide)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
/-- Block `0x2a71`: flag `0xa174` clear: to `0x2a93`. -/
theorem step2a71 {W : World} {b : Word} (I : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64)
    {Q : PState → Prop} {u : PState} (hd : u.g.done = none) (hMA : ShaMainAll b u.m.memory)
    (hrip : u.m.core.rip = b + 0x2a71#64)
    (hl : loadN u.m.memory (u.m.core.rip + 0x7703#64) 1 = some 0#64)
    (k : StepK W Q u (b + 0x2a93#64) u.m.memory) : MustQ W Q u := by
  obtain ⟨-, l1, l2, -⟩ := mainAll_lens
  refine must_piece I hb hd (cb := 10578) (by omega) hMA.ld1 hMA.ro1 blk2a71 blk2a71_ok
    (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp
  rotate_left
  · rename_i v0 h0
    rw [hl] at h0
    cases h0
    exact ⟨true, by decide +kernel⟩
  · exact ⟨_, hl⟩
  rename_i v0 h0 bv hbv
  refine k _ ?_ (Eq.refl _) rfl (fun r => state_read_other (by simp [blk2a71])) rfl
  rw [hl] at h0
  cases h0
  have hb1 : bv = true := by revert bv; decide +kernel
  subst hb1
  blk_simp [blk2a71, hrip]
  rw [ite_t (by decide)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
/-- Block `0x2a93`: flag `0xa173` clear: to `0x2ab5`. -/
theorem step2a93 {W : World} {b : Word} (I : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64)
    {Q : PState → Prop} {u : PState} (hd : u.g.done = none) (hMA : ShaMainAll b u.m.memory)
    (hrip : u.m.core.rip = b + 0x2a93#64)
    (hl : loadN u.m.memory (u.m.core.rip + 0x76e0#64) 1 = some 0#64)
    (k : StepK W Q u (b + 0x2ab5#64) u.m.memory) : MustQ W Q u := by
  obtain ⟨-, l1, l2, -⟩ := mainAll_lens
  refine must_piece I hb hd (cb := 10578) (by omega) hMA.ld1 hMA.ro1 blk2a93 blk2a93_ok
    (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp
  rotate_left
  · rename_i v0 h0
    rw [hl] at h0
    cases h0
    exact ⟨true, by decide +kernel⟩
  · exact ⟨_, hl⟩
  rename_i v0 h0 bv hbv
  refine k _ ?_ (Eq.refl _) rfl (fun r => state_read_other (by simp [blk2a93])) rfl
  rw [hl] at h0
  cases h0
  have hb1 : bv = true := by revert bv; decide +kernel
  subst hb1
  blk_simp [blk2a93, hrip]
  rw [ite_t (by decide)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
/-- Block `0x29fd`: `binary` unset: the two `.bss` words, then (`binary != 0`) to `0x2a29`. -/
theorem step29fd {W : World} {b : Word} (I : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64)
    {Q : PState → Prop} {u : PState} (hd : u.g.done = none) (hMA : ShaMainAll b u.m.memory)
    (hrip : u.m.core.rip = b + 0x29fd#64)
    (hl : loadN u.m.memory (u.m.core.read .rbp + 0xffffffffffffff38#64) 4 = some 0xffffffff#64)
    (hw1 : u.m.memory.Permitted .write (u.m.core.rip + 0x776b#64).toNat 8)
    (hw2 : u.m.memory.Permitted .write (u.m.core.rip + 0x777b#64).toNat 8)
    (k : StepK W Q u (b + 0x2a29#64) (storeMem (storeMem u.m.memory (u.m.core.rip + 0x776b#64) 8 0x42#64)
      (u.m.core.rip + 0x777b#64) 8 0x40#64)) : MustQ W Q u := by
  obtain ⟨-, l1, l2, -⟩ := mainAll_lens
  refine must_piece I hb hd (cb := 0x2952) (by omega) hMA.ld1 hMA.ro1 blk29fd blk29fd_ok
    (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp
  rotate_left
  · rename_i v0 h0
    rw [hl] at h0
    cases h0
    exact ⟨true, by decide +kernel⟩
  · exact hw2
  · exact hw1
  · exact ⟨_, hl⟩
  rename_i v0 h0 bv hbv
  refine k _ ?_ (Eq.refl _) rfl (fun r => state_read_other (by simp [blk29fd])) rfl
  rw [hl] at h0
  cases h0
  have hb1 : bv = true := by revert bv; decide +kernel
  subst hb1
  blk_simp [blk29fd, hrip]
  rw [ite_t (by decide)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
/-- Block `0x2ab5`: `eax = !flag(0xa172)` = 1, to `0x2abf`. -/
theorem step2ab5 {W : World} {b : Word} (I : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64)
    {Q : PState → Prop} {u : PState} (hd : u.g.done = none) (hMA : ShaMainAll b u.m.memory)
    (hrip : u.m.core.rip = b + 0x2ab5#64)
    (hl : loadN u.m.memory (u.m.core.rip + 0x76bd#64) 1 = some 0#64)
    (k : ∀ w, w.m.core.rip = b + 0x2abf#64 → w.m.memory = u.m.memory → w.g = u.g →
      (∀ r, r ≠ .rax → w.m.core.read r = u.m.core.read r) → w.m.core.read .rax = 1#64 →
      w.m.core.fsBase = u.m.core.fsBase → MustQ W Q w) : MustQ W Q u := by
  obtain ⟨-, l1, l2, -⟩ := mainAll_lens
  refine must_piece I hb hd (cb := 0x2952) (by omega) hMA.ld1 hMA.ro1 blk2ab5 blk2ab5_ok
    (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp
  rotate_left
  · exact ⟨_, hl⟩
  rename_i v0 h0
  refine k _ ?_ (Eq.refl _) rfl (fun r hr => state_read_other (by simp [blk2ab5, hr])) ?_ rfl
  · blk_simp [blk2ab5, hrip]
  · rw [hl] at h0
    cases h0
    blk_simp [blk2ab5]
    decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
/-- `0x2abf`: `or al, [rbp-0xe0]` (`--check` off: `al` stays 1, `ZF` clear). -/
theorem gap2abf {W : World} {b : Word} (I : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64)
    {Q : PState → Prop} {u : PState} (hd : u.g.done = none)
    (hC : Loaded u.m.memory (b + 0x29fd#64) mainCText) (hrip : u.m.core.rip = b + 0x2abf#64)
    (hrax : u.m.core.read .rax = 1#64)
    (hl : loadN u.m.memory (u.m.core.read .rbp + BitVec.signExtend 64 0xffffff20#32) 1 = some 0#64)
    (k : ∀ w, w.m.core.rip = b + 0x2ac5#64 → w.m.memory = u.m.memory → w.g = u.g →
      (∀ r, r ≠ .rax → w.m.core.read r = u.m.core.read r) → w.m.core.read .rax = 1#64 →
      Silmaril.X86.Ext.Cond.eval w.m.core.flags .e = some false →
      w.m.core.fsBase = u.m.core.fsBase → MustQ W Q w) : MustQ W Q u := by
  refine must_listed (o := 194) shaM_listing_ok.2.1 rfl hd (by rw [hrip]; exact sha_in' I hb (by decide))
    hC (by rw [hrip, BitVec.add_assoc]; rfl) ?_
  rw [exec_aluR8_mem (by decide) _ _ _ _ (by rw [ofReg_addr]; exact hl), WP_ok]
  refine k _ ?_ rfl rfl (fun r hr => ?_) ?_ ?_ rfl
  · rw [hrip, BitVec.add_assoc]; rfl
  · simp [Silmaril.X86.Ext8.BReg.write, Silmaril.X86.Ext.writeByte, hr]
  · simp [Silmaril.X86.Ext8.BReg.write, Silmaril.X86.Ext8.BReg.read, Silmaril.X86.Ext.writeByte, hrax]
    decide +kernel
  · simp [Silmaril.X86.Ext8.BReg.read, hrax]
    decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
/-- Block `0x2ac5`: `edx = eax` (= 1), `ZF` clear: to `0x2acd`. -/
theorem step2ac5 {W : World} {b : Word} (I : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64)
    {Q : PState → Prop} {u : PState} (hd : u.g.done = none) (hMA : ShaMainAll b u.m.memory)
    (hrip : u.m.core.rip = b + 0x2ac5#64) (hrax : u.m.core.read .rax = 1#64)
    (hz : Silmaril.X86.Ext.Cond.eval u.m.core.flags .e = some false)
    (k : ∀ w, w.m.core.rip = b + 0x2acd#64 → w.m.memory = u.m.memory → w.g = u.g →
      (∀ r, r ≠ .rdx → w.m.core.read r = u.m.core.read r) → w.m.core.read .rdx = 1#64 →
      w.m.core.fsBase = u.m.core.fsBase → MustQ W Q w) : MustQ W Q u := by
  obtain ⟨-, l1, l2, -⟩ := mainAll_lens
  refine must_piece I hb hd (cb := 0x2952) (by omega) hMA.ld1 hMA.ro1 blk2ac5 blk2ac5_ok
    (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp
  rotate_left
  · exact ⟨_, hz⟩
  rename_i bv hbv
  refine k _ ?_ (Eq.refl _) rfl (fun r hr => state_read_other (by simp [blk2ac5, hr])) ?_ rfl
  · rw [hz] at hbv
    cases hbv
    blk_simp [blk2ac5, hrip]
    rw [ite_f (by decide)]
  · blk_simp [blk2ac5, hrax]
    rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
/-- Block `0x2acd`: `eax = !check` = 1, to `0x2ad7`. -/
theorem step2acd {W : World} {b : Word} (I : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64)
    {Q : PState → Prop} {u : PState} (hd : u.g.done = none) (hMA : ShaMainAll b u.m.memory)
    (hrip : u.m.core.rip = b + 0x2acd#64)
    (hl : loadN u.m.memory (u.m.core.read .rbp + 0xffffffffffffff20#64) 1 = some 0#64)
    (k : ∀ w, w.m.core.rip = b + 0x2ad7#64 → w.m.memory = u.m.memory → w.g = u.g →
      (∀ r, r ≠ .rax → w.m.core.read r = u.m.core.read r) → w.m.core.read .rax = 1#64 →
      w.m.core.fsBase = u.m.core.fsBase → MustQ W Q w) : MustQ W Q u := by
  obtain ⟨-, l1, l2, -⟩ := mainAll_lens
  refine must_piece I hb hd (cb := 0x2952) (by omega) hMA.ld1 hMA.ro1 blk2acd blk2acd_ok
    (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp
  rotate_left
  · exact ⟨_, hl⟩
  rename_i v0 h0
  refine k _ ?_ (Eq.refl _) rfl (fun r hr => state_read_other (by simp [blk2acd, hr])) ?_ rfl
  · blk_simp [blk2acd, hrip]
  · rw [hl] at h0
    cases h0
    blk_simp [blk2acd]
    decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
/-- `0x2ad7`: `and al, [flag 0xa170]` (clear: `al = 0`, `ZF` set). -/
theorem gap2ad7 {W : World} {b : Word} (I : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64)
    {Q : PState → Prop} {u : PState} (hd : u.g.done = none)
    (hC : Loaded u.m.memory (b + 0x29fd#64) mainCText) (hrip : u.m.core.rip = b + 0x2ad7#64)
    (hrax : u.m.core.read .rax = 1#64)
    (hl : loadN u.m.memory (u.m.core.rip + BitVec.ofNat 64 6 + BitVec.signExtend 64 0x7693#32) 1 = some 0#64)
    (k : ∀ w, w.m.core.rip = b + 0x2add#64 → w.m.memory = u.m.memory → w.g = u.g →
      (∀ r, r ≠ .rax → w.m.core.read r = u.m.core.read r) → w.m.core.read .rax = 0#64 →
      Silmaril.X86.Ext.Cond.eval w.m.core.flags .ne = some false →
      w.m.core.fsBase = u.m.core.fsBase → MustQ W Q w) : MustQ W Q u := by
  refine must_listed (o := 218) shaM_listing_ok.2.1 rfl hd (by rw [hrip]; exact sha_in' I hb (by decide))
    hC (by rw [hrip, BitVec.add_assoc]; rfl) ?_
  rw [exec_aluR8_mem (by decide) _ _ _ _ (by rw [ofRip_addr]; exact hl), WP_ok]
  refine k _ ?_ rfl rfl (fun r hr => ?_) ?_ ?_ rfl
  · rw [hrip, BitVec.add_assoc]; rfl
  · simp [Silmaril.X86.Ext8.BReg.write, Silmaril.X86.Ext.writeByte, hr]
  · simp [Silmaril.X86.Ext8.BReg.write, Silmaril.X86.Ext8.BReg.read, Silmaril.X86.Ext.writeByte, hrax]
    decide +kernel
  · simp [Silmaril.X86.Ext8.BReg.read, hrax]
    decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
/-- Block `0x2add`: `ZF` set: to `0x2ae3`. -/
theorem step2add {W : World} {b : Word} (I : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64)
    {Q : PState → Prop} {u : PState} (hd : u.g.done = none) (hMA : ShaMainAll b u.m.memory)
    (hrip : u.m.core.rip = b + 0x2add#64)
    (hz : Silmaril.X86.Ext.Cond.eval u.m.core.flags .ne = some false)
    (k : StepK W Q u (b + 0x2ae3#64) u.m.memory) : MustQ W Q u := by
  obtain ⟨-, l1, l2, -⟩ := mainAll_lens
  refine must_piece I hb hd (cb := 0x2952) (by omega) hMA.ld1 hMA.ro1 blk2add blk2add_ok
    (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp
  rotate_left
  · exact ⟨_, hz⟩
  rename_i bv hbv
  refine k _ ?_ (Eq.refl _) rfl (fun r => state_read_other (by simp [blk2add])) rfl
  rw [hz] at hbv
  cases hbv
  blk_simp [blk2add, hrip]
  rw [ite_f (by decide)]

end Silmaril.Elf.Link.Dyn.Sha256sum
