module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.TailArgs

/-! # GNU `sha256sum`: the end of `main` (`0x2b86`, `0x2cf9`–`0x2d30`, `0x36c9`–`0x36ee`)

After `digest_file` (`test al`, to the result line), after the operand loop (`ok` into `edx`,
`have_read_stdin` tested: `rpl_fclose (stdin)` at `0x36c9` when set), the guard check and the
epilogue (`lea rsp, [rbp-0x28]`, six pops, `ret`). One lemma per block (`CertMainAll`), and the
local call of `rpl_fclose` at `0x36d9` (`callFcloseListing`).
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
/-- Block `0x2b86`: `digest_file` returned true (`al = 1`): to the result line `0x2b8a`. -/
theorem step2b86 {W : World} {b : Word} (I : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64)
    {Q : PState → Prop} {u : PState} (hd : u.g.done = none) (hMA : ShaMainAll b u.m.memory)
    (hrip : u.m.core.rip = b + 0x2b86#64) (hal : (u.m.core.read .rax).setWidth 8 = 1#8)
    (k : StepK W Q u (b + 0x2b8a#64) u.m.memory) : MustQ W Q u := by
  obtain ⟨-, l1, l2, -⟩ := mainAll_lens
  refine must_piece I hb hd (cb := 0x2b2c) (by omega) hMA.ld2 hMA.ro2 blk2b86 blk2b86_ok
    (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp
  rotate_left
  · exact eval_some (defined_logic _) _
  rename_i bv hbv
  refine k _ ?_ (Eq.refl _) rfl (fun r => state_read_other (by simp [blk2b86])) rfl
  rw [hal] at hbv
  have hb1 : bv = false := by revert bv; decide +kernel
  subst hb1
  blk_simp [blk2b86, hrip]
  rw [ite_f (by decide)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
/-- Block `0x2cf9`: `edx = eax` (the `ok` byte), to `0x2cfb`. -/
theorem step2cf9 {W : World} {b : Word} (I : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64)
    {Q : PState → Prop} {u : PState} (hd : u.g.done = none) (hMA : ShaMainAll b u.m.memory)
    (hrip : u.m.core.rip = b + 0x2cf9#64)
    (k : ∀ w, w.m.core.rip = b + 0x2cfb#64 → w.m.memory = u.m.memory → w.g = u.g →
      (∀ r, r ≠ .rdx → w.m.core.read r = u.m.core.read r) →
      w.m.core.read .rdx = ((u.m.core.read .rax).setWidth 32).setWidth 64 →
      w.m.core.fsBase = u.m.core.fsBase → MustQ W Q w) : MustQ W Q u := by
  obtain ⟨-, l1, l2, -⟩ := mainAll_lens
  refine must_piece I hb hd (cb := 0x2b2c) (by omega) hMA.ld2 hMA.ro2 blk2cf9 blk2cf9_ok
    (by rw [hrip]; rfl) ?_
  blk_wp
  refine k _ ?_ (Eq.refl _) rfl (fun r hr => state_read_other (by simp [blk2cf9, hr])) ?_ rfl
  · blk_simp [blk2cf9, hrip]
  · blk_simp [blk2cf9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
/-- Block `0x2cfb`: `have_read_stdin` set: to `rpl_fclose (stdin)` at `0x36c9`. -/
theorem step2cfb_t {W : World} {b : Word} (I : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64)
    {Q : PState → Prop} {u : PState} (hd : u.g.done = none) (hMA : ShaMainAll b u.m.memory)
    (hrip : u.m.core.rip = b + 0x2cfb#64) {h : Word}
    (hl : loadN u.m.memory (u.m.core.rip + 0x7465#64) 1 = some h) (hh : h.setWidth 8 ≠ 0#8)
    (k : StepK W Q u (b + 0x36c9#64) u.m.memory) : MustQ W Q u := by
  obtain ⟨-, l1, l2, -⟩ := mainAll_lens
  refine must_piece I hb hd (cb := 0x2b2c) (by omega) hMA.ld2 hMA.ro2 blk2cfb blk2cfb_ok
    (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp
  rotate_left
  · exact eval_some (defined_alu _ _ _ _) _
  · exact ⟨_, hl⟩
  rename_i v0 h0 bv hbv
  refine k _ ?_ (Eq.refl _) rfl (fun r => state_read_other (by simp [blk2cfb])) rfl
  rw [hl] at h0
  cases h0
  have hb1 : bv = true := by
    generalize BitVec.setWidth 8 h = x at hbv hh
    revert bv hh x
    decide +kernel
  subst hb1
  blk_simp [blk2cfb, hrip]
  rw [ite_t (by decide)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
/-- Block `0x2cfb`: `have_read_stdin` clear: to the epilogue `0x2d08`. -/
theorem step2cfb_f {W : World} {b : Word} (I : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64)
    {Q : PState → Prop} {u : PState} (hd : u.g.done = none) (hMA : ShaMainAll b u.m.memory)
    (hrip : u.m.core.rip = b + 0x2cfb#64) {h : Word}
    (hl : loadN u.m.memory (u.m.core.rip + 0x7465#64) 1 = some h) (hh : h.setWidth 8 = 0#8)
    (k : StepK W Q u (b + 0x2d08#64) u.m.memory) : MustQ W Q u := by
  obtain ⟨-, l1, l2, -⟩ := mainAll_lens
  refine must_piece I hb hd (cb := 0x2b2c) (by omega) hMA.ld2 hMA.ro2 blk2cfb blk2cfb_ok
    (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp
  rotate_left
  · exact eval_some (defined_alu _ _ _ _) _
  · exact ⟨_, hl⟩
  rename_i v0 h0 bv hbv
  refine k _ ?_ (Eq.refl _) rfl (fun r => state_read_other (by simp [blk2cfb])) rfl
  rw [hl] at h0
  cases h0
  rw [hh] at hbv
  have hb1 : bv = false := by revert bv; decide +kernel
  subst hb1
  blk_simp [blk2cfb, hrip]
  rw [ite_f (by decide)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
/-- Block `0x36c9`: `ok` saved at `rbp-0xc8`, `rdi = stdin` (libc's variable through the GOT), to
the call of `rpl_fclose` at `0x36d9`. -/
theorem step36c9 {W : World} {b : Word} (I : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64)
    {Q : PState → Prop} {u : PState} (hd : u.g.done = none) (hMA : ShaMainAll b u.m.memory)
    (hrip : u.m.core.rip = b + 0x36c9#64) {V F : Word}
    (hgot : loadN u.m.memory (u.m.core.rip + 0x68ef#64) 8 = some V)
    (hw : u.m.memory.Permitted .write (u.m.core.read .rbp + 0xffffffffffffff38#64).toNat 1)
    (hv : loadN (storeMem u.m.memory (u.m.core.read .rbp + 0xffffffffffffff38#64) 1
      (((u.m.core.read .rdx).setWidth 8).setWidth 64)) V 8 = some F)
    (k : ∀ w, w.m.core.rip = b + 0x36d9#64 →
      w.m.memory = storeMem u.m.memory (u.m.core.read .rbp + 0xffffffffffffff38#64) 1
        (((u.m.core.read .rdx).setWidth 8).setWidth 64) → w.g = u.g →
      (∀ r, r ≠ .rax → r ≠ .rdi → w.m.core.read r = u.m.core.read r) → w.m.core.read .rdi = F →
      w.m.core.fsBase = u.m.core.fsBase → MustQ W Q w) : MustQ W Q u := by
  obtain ⟨-, -, -, -, -, -, -, l7, -⟩ := mainAll_lens
  refine must_piece I hb hd (cb := 0x34f6) (by omega) hMA.ld7 hMA.ro7 blk36c9 blk36c9_ok
    (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp
  rotate_left
  · rename_i v0 h0
    rw [hgot] at h0; cases h0; exact ⟨_, hv⟩
  · exact hw
  · exact ⟨_, hgot⟩
  rename_i v0 h0 v1 h1
  refine k _ ?_ (Eq.refl _) rfl (fun r h1 h2 => state_read_other (by simp [blk36c9, h1, h2])) ?_ rfl
  · blk_simp [blk36c9, hrip]
  · rw [hgot] at h0; cases h0; rw [hv] at h1; cases h1; blk_simp [blk36c9]

/-- The call of `rpl_fclose` at `0x36d9` (`call 0x42b0`). -/
def callFcloseListing : List (Nat × Silmaril.X86.Ext9.Instr × Nat) :=
  [(0x1e3, .ext8 (.base (.call 0xbd2#32)), 5)]

theorem callFclose_ok : listingOk mainAll7Text callFcloseListing = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
/-- `0x36d9`: `call rpl_fclose`: the return address `0x36de` pushed, control at `0x42b0`. -/
theorem call36d9 {W : World} {b : Word} (I : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64)
    {Q : PState → Prop} {u : PState} (hd : u.g.done = none) (hMA : ShaMainAll b u.m.memory)
    (hrip : u.m.core.rip = b + 0x36d9#64)
    (hw : u.m.memory.Permitted .write (u.m.core.read .rsp - 8#64).toNat 8)
    (k : MustQ W Q ⟨⟨{ u.m.core.write .rsp (u.m.core.read .rsp - 8#64) with rip := b + 0x42b0#64 },
      pushMem u.m.memory (u.m.core.read .rsp) (b + 0x36de#64)⟩, u.g⟩) : MustQ W Q u := by
  refine must_listed (o := 0x1e3) callFclose_ok rfl hd (by rw [hrip]; exact sha_in' I hb (by decide))
    hMA.ld7 (by rw [hrip, BitVec.add_assoc]; rfl) ?_
  rw [exec_call _ _ _ _ hw, WP_ok, hrip,
    show b + 0x36d9#64 + BitVec.ofNat 64 5 + BitVec.signExtend 64 0xbd2#32 = b + 0x42b0#64 by
      rw [BitVec.add_assoc, BitVec.add_assoc]; rfl,
    show b + 0x36d9#64 + BitVec.ofNat 64 5 = b + 0x36de#64 by rw [BitVec.add_assoc]; rfl]
  exact k

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
/-- Block `0x36de`: `rpl_fclose` returned 0 (`eax + 1 ≠ 0`): `edx = ok`, to the epilogue `0x2d08`. -/
theorem step36de {W : World} {b : Word} (I : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64)
    {Q : PState → Prop} {u : PState} (hd : u.g.done = none) (hMA : ShaMainAll b u.m.memory)
    (hrip : u.m.core.rip = b + 0x36de#64) (hax : (u.m.core.read .rax).setWidth 32 = 0#32) {d : Word}
    (hl : loadN u.m.memory (u.m.core.read .rbp + 0xffffffffffffff38#64) 1 = some d)
    (k : ∀ w, w.m.core.rip = b + 0x2d08#64 → w.m.memory = u.m.memory → w.g = u.g →
      (∀ r, r ≠ .rax → r ≠ .rdx → w.m.core.read r = u.m.core.read r) →
      w.m.core.read .rdx = (((d.setWidth 8).setWidth 64).setWidth 32).setWidth 64 →
      w.m.core.fsBase = u.m.core.fsBase → MustQ W Q w) : MustQ W Q u := by
  obtain ⟨-, -, -, -, -, -, -, l7, -⟩ := mainAll_lens
  refine must_piece I hb hd (cb := 0x34f6) (by omega) hMA.ld7 hMA.ro7 blk36de blk36de_ok
    (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp
  rotate_left
  · exact eval_some (defined_alu _ _ _ _) _
  · exact ⟨_, hl⟩
  rename_i v0 h0 bv hbv
  rw [hl] at h0; cases h0
  refine k _ ?_ (Eq.refl _) rfl (fun r h1 h2 => state_read_other (by simp [blk36de, h1, h2])) ?_ rfl
  · rw [hax] at hbv
    have hb1 : bv = true := by revert bv; decide +kernel
    subst hb1
    blk_simp [blk36de, hrip]
    rw [ite_t (by decide)]
    exact congrArg (b + ·) rfl
  · blk_simp [blk36de]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
/-- Block `0x2d08`: `eax = !ok` (`edx = 1`: 0), the guard intact: to the epilogue's pops `0x2d21`. -/
theorem step2d08 {W : World} {b : Word} (I : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64)
    {Q : PState → Prop} {u : PState} (hd : u.g.done = none) (hMA : ShaMainAll b u.m.memory)
    (hrip : u.m.core.rip = b + 0x2d08#64) (hdx : (u.m.core.read .rdx).setWidth 8 = 1#8) {g : Word}
    (hg1 : loadN u.m.memory (u.m.core.read .rbp + 0xffffffffffffffc8#64) 8 = some g)
    (hg2 : loadN u.m.memory (u.m.core.fsBase + 0x28#64) 8 = some g)
    (k : ∀ w, w.m.core.rip = b + 0x2d21#64 → w.m.memory = u.m.memory → w.g = u.g →
      (∀ r, r ≠ .rax → r ≠ .rdx → w.m.core.read r = u.m.core.read r) → low32 (w.m.core.read .rax) = 0#32 →
      w.m.core.fsBase = u.m.core.fsBase → MustQ W Q w) : MustQ W Q u := by
  obtain ⟨-, l1, l2, -⟩ := mainAll_lens
  refine must_piece I hb hd (cb := 0x2b2c) (by omega) hMA.ld2 hMA.ro2 blk2d08 blk2d08_ok
    (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp
  rotate_left
  · exact eval_some (defined_alu _ _ _ _) _
  · exact ⟨_, hg2⟩
  · exact ⟨_, hg1⟩
  rename_i v0 h0 v1 h1 bv hbv
  rw [hg1] at h0; cases h0; rw [hg2] at h1; cases h1
  refine k _ ?_ (Eq.refl _) rfl (fun r h1 h2 => state_read_other (by simp [blk2d08, h1, h2])) ?_ rfl
  · have hb1 : bv = false := by
      simp only [Silmaril.X86.Ext.AluOp.flagsN, BitVec.setWidth_eq] at hbv
      rw [Silmaril.X86.Ext.eval_subFlagsN (w := 63)] at hbv
      simpa [Silmaril.X86.Ext.Cond.afterCmp] using hbv.symm
    subst hb1
    blk_simp [blk2d08, hrip]
    rw [ite_f (by decide)]
  · blk_simp [blk2d08]
    simp only [low32]
    exact low8_xor1 _ hdx

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
/-- Block `0x2d08` for `ok ∈ {0, 1}` (K8): `eax = !ok`, the guard intact: to `0x2d21`. -/
theorem step2d08o {W : World} {b : Word} (I : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64)
    {Q : PState → Prop} {u : PState} (hd : u.g.done = none) (hMA : ShaMainAll b u.m.memory)
    (hrip : u.m.core.rip = b + 0x2d08#64) {d : BitVec 8} (hdx : (u.m.core.read .rdx).setWidth 8 = d) (hd01 : d = 0#8 ∨ d = 1#8) {g : Word}
    (hg1 : loadN u.m.memory (u.m.core.read .rbp + 0xffffffffffffffc8#64) 8 = some g)
    (hg2 : loadN u.m.memory (u.m.core.fsBase + 0x28#64) 8 = some g)
    (k : ∀ w, w.m.core.rip = b + 0x2d21#64 → w.m.memory = u.m.memory → w.g = u.g →
      (∀ r, r ≠ .rax → r ≠ .rdx → w.m.core.read r = u.m.core.read r) → low32 (w.m.core.read .rax) = (if d = 1#8 then 0#32 else 1#32) →
      w.m.core.fsBase = u.m.core.fsBase → MustQ W Q w) : MustQ W Q u := by
  obtain ⟨-, l1, l2, -⟩ := mainAll_lens
  refine must_piece I hb hd (cb := 0x2b2c) (by omega) hMA.ld2 hMA.ro2 blk2d08 blk2d08_ok
    (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp
  rotate_left
  · exact eval_some (defined_alu _ _ _ _) _
  · exact ⟨_, hg2⟩
  · exact ⟨_, hg1⟩
  rename_i v0 h0 v1 h1 bv hbv
  rw [hg1] at h0; cases h0; rw [hg2] at h1; cases h1
  refine k _ ?_ (Eq.refl _) rfl (fun r h1 h2 => state_read_other (by simp [blk2d08, h1, h2])) ?_ rfl
  · have hb1 : bv = false := by
      simp only [Silmaril.X86.Ext.AluOp.flagsN, BitVec.setWidth_eq] at hbv
      rw [Silmaril.X86.Ext.eval_subFlagsN (w := 63)] at hbv
      simpa [Silmaril.X86.Ext.Cond.afterCmp] using hbv.symm
    subst hb1
    blk_simp [blk2d08, hrip]
    rw [ite_f (by decide)]
  · blk_simp [blk2d08]
    simp only [low32]
    exact low8_xorB _ hdx hd01

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
/-- Block `0x2d21`: `lea rsp, [rbp-0x28]`, the six pops and `ret`. -/
theorem step2d21 {W : World} {b : Word} (I : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64)
    {Q : PState → Prop} {u : PState} (hd : u.g.done = none) (hMA : ShaMainAll b u.m.memory)
    (hrip : u.m.core.rip = b + 0x2d21#64) {w1 w2 w3 w4 w5 w6 w7 : Word}
    (h1 : (u.m.memory.readBytes (u.m.core.read .rbp + 0xffffffffffffffd8#64).toNat 8).bind
      Silmaril.X86.wordOfBytes? = some w1)
    (h2 : (u.m.memory.readBytes (u.m.core.read .rbp + 0xffffffffffffffe0#64).toNat 8).bind
      Silmaril.X86.wordOfBytes? = some w2)
    (h3 : (u.m.memory.readBytes (u.m.core.read .rbp + 0xffffffffffffffe8#64).toNat 8).bind
      Silmaril.X86.wordOfBytes? = some w3)
    (h4 : (u.m.memory.readBytes (u.m.core.read .rbp + 0xfffffffffffffff0#64).toNat 8).bind
      Silmaril.X86.wordOfBytes? = some w4)
    (h5 : (u.m.memory.readBytes (u.m.core.read .rbp + 0xfffffffffffffff8#64).toNat 8).bind
      Silmaril.X86.wordOfBytes? = some w5)
    (h6 : (u.m.memory.readBytes (u.m.core.read .rbp + 0#64).toNat 8).bind
      Silmaril.X86.wordOfBytes? = some w6)
    (h7 : (u.m.memory.readBytes (u.m.core.read .rbp + 8#64).toNat 8).bind
      Silmaril.X86.wordOfBytes? = some w7)
    (k : ∀ w, w.m.core.rip = w7 → w.m.memory = u.m.memory → w.g = u.g →
      w.m.core.read .rsp = u.m.core.read .rbp + 0x10#64 → (∀ r, r ≠ .rbx → r ≠ .rsp →
        r ≠ .rbp → r ≠ .r12 → r ≠ .r13 → r ≠ .r14 → r ≠ .r15 → w.m.core.read r = u.m.core.read r) →
      w.m.core.fsBase = u.m.core.fsBase → MustQ W Q w) : MustQ W Q u := by
  obtain ⟨-, -, -, l3, -⟩ := mainAll_lens
  refine must_piece I hb hd (cb := 0x2d21) (by omega) hMA.ld3 hMA.ro3 blk2d21 blk2d21_ok
    (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp
  rotate_left
  · exact ⟨_, h7⟩
  · exact ⟨_, h6⟩
  · exact ⟨_, h5⟩
  · exact ⟨_, h4⟩
  · exact ⟨_, h3⟩
  · exact ⟨_, h2⟩
  · exact ⟨_, h1⟩
  rename_i v1 e1 v2 e2 v3 e3 v4 e4 v5 e5 v6 e6 v7 e7
  refine k _ ?_ (Eq.refl _) rfl ?_
    (fun r a2 a3 a4 a5 a6 a7 a8 => state_read_other (by simp [blk2d21, a2, a3, a4, a5, a6, a7, a8])) rfl
  · rw [h7] at e7; cases e7; blk_simp [blk2d21]
  · blk_simp [blk2d21]

end Silmaril.Elf.Link.Dyn.Sha256sum
