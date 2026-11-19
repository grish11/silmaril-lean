module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.TailRun2
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.TailEnd
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.CloseIn

/-! # GNU `sha256sum`, stdin tier: `main` from the end of the result line (`0x2c8a`) to its return

`tail_end`: back to the loop's head, the end of the operands (`0x2cf9`), `have_read_stdin`
set (`0x2cfb`), `rpl_fclose (stdin)` (`0x36c9`–`0x36de`, `sha_rplFclose_in'`), the stack guard
(`0x2d08`) and the epilogue (`0x2d21`): `main` returns 0 to its caller's return address.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.X86.FnContract (AbiEntry AbiReturn)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Streams
open Silmaril.Elf.Link.Dyn.Cert

theorem sw_a (x : Word) : ((x.setWidth 32).setWidth 64).setWidth 8 = x.setWidth 8 := by
  ext i hi; simp [BitVec.getElem_setWidth]
theorem sw_b (x : Word) : ((x.setWidth 8).setWidth 64).setWidth 8 = x.setWidth 8 := by
  ext i hi; simp [BitVec.getElem_setWidth]
theorem sw_c (x : Word) :
    BitVec.ofNat 64 (((x.setWidth 8).setWidth 64 : Word).toNat % 2 ^ (8 * 1)) = (x.setWidth 8).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq; simp

theorem loadN_store1 {m : Memory} {a v : Word} (hr : m.Permitted .read a.toNat 1) :
    loadN (storeMem m a 1 v) a 1 = some (BitVec.ofNat 64 (v.toNat % 2 ^ (8 * 1))) := by
  simp only [loadN, storeMem_read hr, Option.map_some, Silmaril.X86.Ext.leValue_leBytes]

theorem ult_end {av : Word} (h : av.toNat + 16 < 2 ^ 64) : (av + 8#64 + 8#64).ult (av + 16#64) = false := by
  have e1 : (av + 8#64).toNat = av.toNat + 8 := addr_toNat (v := 8) (by omega)
  have e2 : (av + 8#64 + 8#64).toNat = av.toNat + 16 := by rw [addr_toNat (v := 8) (by rw [e1]; omega), e1]
  have e3 : (av + 16#64).toNat = av.toNat + 16 := addr_toNat (v := 16) (by omega)
  simp only [BitVec.ult, e2, e3]; simp

theorem word_rb {m : Memory} {a : Nat} {v : Word}
    (h : m.readBytes a 8 = some (Silmaril.Machine.LittleEndian.encodeWords [v])) :
    (m.readBytes a 8).bind Silmaril.X86.wordOfBytes? = some v := by
  rw [h]; simp

theorem loadN_enc {m : Memory} {A : Word} {v : Word}
    (h : m.readBytes A.toNat 8 = some (Silmaril.Machine.LittleEndian.encodeWords [v])) : loadN m A 8 = some v := by
  simp only [loadN, h, Option.map_some, ← Silmaril.X86.Ext.leBytes_eight, Silmaril.X86.Ext.leValue_leBytes]
  congr 1; apply BitVec.eq_of_toNat_eq; simp [v.isLt]


open Silmaril.X86 in
/-- `0x2c8a`–`0x2c96` as a block of `mainAll2Text` (`movzbl eax, byte [rbp-0xd8]`, `jmp 0x2b57`). -/
def blk2c8aT : Silmaril.Elf.Link.Dyn.Cert.Blk where
  off := 350
  L := [
    (Bir9.LInstr.ext (Ext.Instr.movx false (Ext.Sz.d) (Ext.Narrow.b) (Reg.rax) (Ext.RM.mem (Ext.Mem.ofReg (Reg.rbp) Option.none 0xffffff28#32))), 7),
    (Bir9.LInstr.ext (Ext.Instr.jmp 0xfffffec1#32), 5)]
  b := { stmts := [Bir9.Stmt.load 1 (Bir9.E.add (Bir9.E.reg (Reg.rbp)) (Bir9.E.imm 0xffffffffffffff28#64))], regs := [(Reg.rax, Bir9.E.zext 32 (Bir9.E.zext 8 (Bir9.E.v 0)))], flags := Bir9.F.entry, rip := Bir9.E.add (Bir9.E.rip) (Bir9.E.imm 0xfffffffffffffecd#64), xmm := [] }

theorem blk2c8aT_ok : blk2c8aT.ok mainAll2Text = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
/-- Block `0x2c8a`: `eax = ok`, back to the loop's head `0x2b57`. -/
theorem step2c8a {W : World} {b : Word} (I : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64)
    {Q : PState → Prop} {u : PState} (hd : u.g.done = none) (hMA : ShaMainAll b u.m.memory)
    (hrip : u.m.core.rip = b + 0x2c8a#64) {ok : Word}
    (hok : loadN u.m.memory (u.m.core.read .rbp + 0xffffffffffffff28#64) 1 = some ok)
    (k : ∀ w, w.m.core.rip = b + 0x2b57#64 → w.m.memory = u.m.memory → w.g = u.g →
      (∀ r, r ≠ .rax → w.m.core.read r = u.m.core.read r) →
      (w.m.core.read .rax).setWidth 8 = ok.setWidth 8 → w.m.core.fsBase = u.m.core.fsBase → MustQ W Q w) :
    MustQ W Q u := by
  obtain ⟨-, -, l2, -⟩ := mainAll_lens
  refine must_piece I hb hd (cb := 0x2b2c) (by omega) hMA.ld2 hMA.ro2 blk2c8aT blk2c8aT_ok
    (by rw [hrip]; rfl) ?_
  blk_wp
  all_goals blk_simp
  rotate_left
  · exact ⟨_, hok⟩
  rename_i v0 h0
  rw [hok] at h0; cases h0
  refine k _ ?_ (Eq.refl _) rfl (fun r h => state_read_other (by simp [blk2c8aT, h])) ?_ rfl
  · blk_simp [blk2c8aT, hrip]; bv_omega
  · blk_simp [blk2c8aT]; bv_omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
/-- Block `0x2b57` at the end of the operands: to `0x2cf9`. -/
theorem step2b57e {W : World} {b : Word} (I : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64)
    {Q : PState → Prop} {u : PState} (hd : u.g.done = none) (hMA : ShaMainAll b u.m.memory)
    (hrip : u.m.core.rip = b + 0x2b57#64) {endp : Word}
    (hend : loadN u.m.memory (u.m.core.read .rbp + 0xffffffffffffff18#64) 8 = some endp)
    (hc : (u.m.core.read .r15 + 8#64).ult endp = false)
    (k : ∀ w, w.m.core.rip = b + 0x2cf9#64 → w.m.memory = u.m.memory → w.g = u.g →
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

theorem fp_neg (sp : Word) (k : Nat) (h : 8 + k ≤ sp.toNat) (hk0 : 0 < k) (hk : k < 2 ^ 64) :
    (sp - 8#64 + BitVec.ofNat 64 (2 ^ 64 - k)).toNat = sp.toNat - 8 - k := by
  have e8 : (sp - 8#64).toNat = sp.toNat - 8 := sub_toNat (k := 8) (by omega) (by decide)
  have := neg_off (fp := sp - 8#64) (k := k) (by rw [e8]; omega) hk0 hk
  rw [this, e8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`main` from `0x2c8a` (after the result line) to its return**, stdin tier: the loop ends,
`rpl_fclose (stdin)` succeeds, `main` returns 0 to the address at its entry stack pointer. -/
theorem tail_end {E : Env} {W : World} {b lb kb sr sc : Word} (cl : CloseImps E W b lb)
    (hls : ImpOk W (lb + 0x11b2a0#64) (nm "lseek") (lseekStep E W)) {Q : PState → Prop}
    {sB x : PState} {sp av g Fi R : Word} (hspB : sB.m.core.read .rsp = sp)
    (hB : Body W (ShaMemAll b lb kb sr sc) sB x 328 4096 (sv6 sB)) (hMA : ShaMainAll b x.m.memory)
    (hrip : x.m.core.rip = b + 0x2c8a#64) (hrbp : x.m.core.read .rbp = sp - 8#64)
    (hlo : E.S.lo + 4096 ≤ sp.toNat) (hal : sp.toNat % 16 = 8)
    (hr15 : x.m.core.read .r15 = av + 8#64) (hav : av.toNat + 16 < 2 ^ 64)
    (hend : loadN x.m.memory (sp - 8#64 + 0xffffffffffffff18#64) 8 = some (av + 16#64))
    (hok : loadN x.m.memory (sp - 8#64 + 0xffffffffffffff28#64) 1 = some 1#64)
    (hhr : loadN x.m.memory (b + 0xa160#64) 1 = some 1#64)
    (hvar : loadN x.m.memory (lb + 0x2056b0#64) 8 = some Fi)
    (hvarK : ∀ j, j < 8 → W.Kept ((lb + 0x2056b0#64).toNat + j))
    {st : St} (hfi : E.S.file x.m.memory Fi st) (hrd : st.reading = true) (herr : st.err = false)
    (hfd : st.fd ≠ 1) (hfd' : st.fd < 2 ^ 31)
    (hgs : x.m.memory.readBytes (sp.toNat - 64) 8 = some (Silmaril.Machine.LittleEndian.encodeWords [g]))
    (hg : loadN x.m.memory (x.m.core.fsBase + 0x28#64) 8 = some g)
    (hgk : ∀ j, j < 8 → W.Kept ((x.m.core.fsBase + 0x28#64).toNat + j))
    (hret : x.m.memory.readBytes sp.toNat 8 = some (Silmaril.Machine.LittleEndian.encodeWords [R]))
    (k : ∀ t, t.m.core.rip = R → low32 (t.m.core.read .rax) = 0#32 →
      t.g.out = x.g.out → t.g.jobs = x.g.jobs → t.g.atexit = x.g.atexit → t.g.done = none →
      Keeps W.Kept x.m.memory t.m.memory →
      (∀ f st', f ≠ Fi → E.S.file x.m.memory f st' → E.S.file t.m.memory f st') →
      t.m.core.fsBase = x.m.core.fsBase → MustQ W Q t) : MustQ W Q x := by
  have I := cl.img
  have hb := cl.hb
  have hroom := hB.room
  rw [hspB] at hroom
  have hsp := hroom.1
  have hsp2 := hroom.2.1
  have hxsp : x.m.core.read .rsp = sp - 328#64 := by rw [hB.rsp, hspB]
  have e8 : (sp - 8#64).toNat = sp.toNat - 8 := sub_toNat (k := 8) (by omega) (by decide)
  have e328 : (x.m.core.read .rsp).toNat = sp.toNat - 328 := by rw [hxsp]; exact sub_toNat (k := 328) (by omega) (by decide)
  have e336 : (x.m.core.read .rsp - 8#64).toNat = sp.toNat - 336 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), e328]; omega
  have hfp : 0x100 ≤ (sp - 8#64).toNat := by rw [e8]; omega
  have eC8 : (sp - 8#64 + 0xffffffffffffff38#64).toNat = sp.toNat - 208 := by
    have := neg_off (fp := sp - 8#64) (k := 0xc8) (by rw [e8]; omega) (by decide) (by decide)
    rw [e8] at this; exact this.trans (by omega)
  have hKroom : ∀ a, sp.toNat - 4096 ≤ a → a < sp.toNat + 8 → ¬ W.Kept a := fun a h1 h2 =>
    (hroom.2.2 a h1 h2).2.2
  -- the loop's last turn
  have hd := hB.done
  refine step2c8a I hb hd hMA hrip (ok := 1#64) (by rw [hrbp]; exact hok) ?_
  intro v1 r1 m1 g1 R1 al1 f1
  have hd1 : v1.g.done = none := by rw [g1]; exact hd
  have r15v : v1.m.core.read .r15 = av + 8#64 := by rw [R1 _ (by decide)]; exact hr15
  refine step2b57e I hb hd1 (m1 ▸ hMA) r1 (endp := av + 16#64)
    (by rw [m1, R1 _ (by decide), hrbp]; exact hend) (by rw [r15v]; exact ult_end hav) ?_
  intro v2 r2 m2 g2 R2 q2 f2
  have hm2 : v2.m.memory = x.m.memory := m2.trans m1
  have hd2 : v2.g.done = none := by rw [g2]; exact hd1
  refine step2cf9 I hb hd2 (hm2 ▸ hMA) r2 ?_
  intro v3 r3 m3 g3 R3 d3 f3
  have hm3 : v3.m.memory = x.m.memory := m3.trans hm2
  have hd3 : v3.g.done = none := by rw [g3]; exact hd2
  refine step2cfb_t I hb hd3 (hm3 ▸ hMA) r3 (h := 1#64)
    (by rw [r3, hm3, show b + 0x2cfb#64 + 0x7465#64 = b + 0xa160#64 by rw [BitVec.add_assoc]; rfl]; exact hhr)
    (by decide) ?_
  intro v4 r4 m4 g4 R4 f4
  have hm4 : v4.m.memory = x.m.memory := m4.trans hm3
  have hd4 : v4.g.done = none := by rw [g4]; exact hd3
  have bp4 : v4.m.core.read .rbp = sp - 8#64 := by
    rw [R4, R3 _ (by decide), R2 _ (by decide) (by decide), R1 _ (by decide), hrbp]
  have sp4 : v4.m.core.read .rsp = sp - 328#64 := by
    rw [R4, R3 _ (by decide), R2 _ (by decide) (by decide), R1 _ (by decide), hxsp]
  have dl4 : (v4.m.core.read .rdx).setWidth 8 = 1#8 := by
    rw [R4, d3, sw_a, R2 _ (by decide) (by decide), al1]; rfl
  -- the store at rbp - 0xc8 and what it keeps
  have hwC8 : x.m.memory.Permitted .write (sp - 8#64 + 0xffffffffffffff38#64).toNat 1 := by
    rw [eC8]; exact room_perm hroom (Or.inr rfl) (by omega) (by omega)
  have hrC8 : x.m.memory.Permitted .read (sp - 8#64 + 0xffffffffffffff38#64).toNat 1 := by
    rw [eC8]; exact room_perm hroom (Or.inl rfl) (by omega) (by omega)
  have hvarD : (lb + 0x2056b0#64).toNat + 8 ≤ (sp - 8#64 + 0xffffffffffffff38#64).toNat ∨
      (sp - 8#64 + 0xffffffffffffff38#64).toNat + 1 ≤ (lb + 0x2056b0#64).toNat := by
    rw [eC8]; by_contra hc
    have := hvarK (sp.toNat - 208 - (lb + 0x2056b0#64).toNat) (by omega)
    rw [show (lb + 0x2056b0#64).toNat + (sp.toNat - 208 - (lb + 0x2056b0#64).toNat) = sp.toNat - 208 by omega] at this
    exact hKroom _ (by omega) (by omega) this
  have hvC : ∀ v, loadN (storeMem x.m.memory (sp - 8#64 + 0xffffffffffffff38#64) 1 v) (lb + 0x2056b0#64) 8 =
      some Fi := fun v => (loadN_storeMem_ne hvarD.symm).trans hvar
  refine step36c9 I hb hd4 (hm4 ▸ hMA) r4 (V := lb + 0x2056b0#64) (F := Fi)
    (by rw [r4, hm4, show b + 0x36c9#64 + 0x68ef#64 = b + 0x9fb8#64 by rw [BitVec.add_assoc]; rfl]
        exact hB.mem.mn.stdinV)
    (by rw [hm4, bp4]; exact hwC8)
    (by rw [hm4, bp4]; exact hvC _) ?_
  intro v5 r5 m5 g5 R5 i5 f5
  have hm5 : v5.m.memory = storeMem x.m.memory (sp - 8#64 + 0xffffffffffffff38#64) 1
      (((v4.m.core.read .rdx).setWidth 8).setWidth 64) := by rw [m5, hm4, bp4]
  have hd5 : v5.g.done = none := by rw [g5]; exact hd4
  have sp5 : v5.m.core.read .rsp = sp - 328#64 := by rw [R5 _ (by decide) (by decide)]; exact sp4
  have bp5 : v5.m.core.read .rbp = sp - 8#64 := by rw [R5 _ (by decide) (by decide)]; exact bp4
  have e5 : (v5.m.core.read .rsp - 8#64).toNat = sp.toNat - 336 := by rw [sp5, ← hxsp]; exact e336
  have hImg : ∀ a, ShaImg b a → a < sp.toNat - 4096 ∨ sp.toNat + 8 ≤ a := fun a ha => by
    by_contra hc; exact hKroom a (by omega) (by omega) (Or.inl (by rw [I]; exact ha))
  have hKs : Keeps W.Kept x.m.memory (storeMem x.m.memory (sp - 8#64 + 0xffffffffffffff38#64) 1
      (((v4.m.core.read .rdx).setWidth 8).setWidth 64)) := storeMem_keeps fun a ha => by
    rw [eC8]; by_contra hc; exact hKroom a (by omega) (by omega) ha
  have hKp : Keeps W.Kept (storeMem x.m.memory (sp - 8#64 + 0xffffffffffffff38#64) 1
      (((v4.m.core.read .rdx).setWidth 8).setWidth 64))
      (pushMem (storeMem x.m.memory (sp - 8#64 + 0xffffffffffffff38#64) 1
        (((v4.m.core.read .rdx).setWidth 8).setWidth 64)) (v5.m.core.read .rsp) (b + 0x36de#64)) :=
    pushMem_keeps fun a ha => by
      rw [e5]; by_contra hc; exact hKroom a (by omega) (by omega) ha
  have hIs : Keeps (ImgW b) x.m.memory (storeMem x.m.memory (sp - 8#64 + 0xffffffffffffff38#64) 1
      (((v4.m.core.read .rdx).setWidth 8).setWidth 64)) :=
    hKs.mono fun a ha => Or.inl (by rw [I]; exact ha.1)
  have hMA5 : ShaMainAll b v5.m.memory := by rw [hm5]; exact hMA.keepW hb hIs
  refine call36d9 I hb hd5 hMA5 r5 (by rw [hm5, e5]; exact room_perm hroom (a := sp.toNat - 336) (len := 8) (Or.inr rfl) (by omega) (by omega)) ?_
  change MustQ W Q (callEntry v5 (b + 0x42b0#64) (b + 0x36de#64))
  have cm : (callEntry v5 (b + 0x42b0#64) (b + 0x36de#64)).m.memory =
      pushMem (storeMem x.m.memory (sp - 8#64 + 0xffffffffffffff38#64) 1
        (((v4.m.core.read .rdx).setWidth 8).setWidth 64)) (v5.m.core.read .rsp) (b + 0x36de#64) := by
    rw [callEntry_mem, hm5]
  have csp : ((callEntry v5 (b + 0x42b0#64) (b + 0x36de#64)).m.core.read .rsp).toNat = sp.toNat - 336 := by
    rw [callEntry_rsp]; exact e5
  have hpr : (callEntry v5 (b + 0x42b0#64) (b + 0x36de#64)).m.memory.readBytes
      ((callEntry v5 (b + 0x42b0#64) (b + 0x36de#64)).m.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [b + 0x36de#64]) := by
    rw [callEntry_rsp, callEntry_mem]
    exact pushMem_read (by rw [e5, hm5]; exact storeMem_permitted.2 (room_perm hroom (a := sp.toNat - 336) (len := 8) (Or.inl rfl) (by omega) (by omega)))
      (by rw [e5, hm5]; exact storeMem_permitted.2 (room_perm hroom (a := sp.toNat - 336) (len := 8) (Or.inr rfl) (by omega) (by omega)))
  have habi : AbiEntry (callEntry v5 (b + 0x42b0#64) (b + 0x36de#64)).m.core
      (callEntry v5 (b + 0x42b0#64) (b + 0x36de#64)).m.memory := Silmaril.Elf.Link.Dyn.Hello.abiEntry_of (by rw [csp]; omega) hpr
  have hKc : Keeps W.Kept x.m.memory (callEntry v5 (b + 0x42b0#64) (b + 0x36de#64)).m.memory := by
    rw [cm]; exact hKs.trans hKp
  have hfile : ∀ f st', E.S.file x.m.memory f st' →
      E.S.file (callEntry v5 (b + 0x42b0#64) (b + 0x36de#64)).m.memory f st' := fun f st' hf => by
    rw [cm]
    refine file_push ?_ (by rw [e5]; omega)
    exact (E.S.local_ _ _ _ _ (storeMem_keeps fun a ha => by
      have := E.S.foot_lo _ _ _ _ hf ha; rw [eC8]; omega) hf).1
  have hpe : ∀ acc a, (callEntry v5 (b + 0x42b0#64) (b + 0x36de#64)).m.memory.permits acc a =
      x.m.memory.permits acc a := fun _ _ => by rw [callEntry_mem, hm5]; rfl
  have hrdi : (callEntry v5 (b + 0x42b0#64) (b + 0x36de#64)).m.core.read .rdi = Fi := by
    rw [callEntry_read _ _ _ (by decide)]; exact i5
  refine sha_rplFclose_in' cl hls (st := st) rfl habi
    ⟨by rw [csp]; omega, by rw [csp]; omega, fun a h1 h2 => by
      rw [csp] at h1 h2; rw [hpe, hpe]; exact hroom.2.2 a (by omega) (by omega)⟩
    (by rw [csp]; omega) hd5 (by rw [cm]; exact hB.mem.cl.keepW hb ((hKs.trans hKp).mono fun a ha => Or.inl (by rw [I]; exact ha.1)))
    (by rw [hrdi]; exact hfile _ _ hfi) hrd herr hfd hfd' ?_
  intro t1 hab hk1 go gj ga gd gi ge gc hax hOK hfs hperm _
  -- what the call keeps
  have hKK : Keeps W.Kept x.m.memory t1.m.memory := hKc.trans (hk1.mono fun a ha => Or.inl ha)
  have hread : ∀ a n, sp.toNat - 200 ≤ a → a + n ≤ sp.toNat + 8 →
      t1.m.memory.readBytes a n = x.m.memory.readBytes a n := by
    intro a n h1 h2
    rw [hk1.readBytes (fun j hj => Or.inr (by rw [csp]; omega)), cm,
      (pushMem_keeps (P := fun y => a ≤ y ∧ y < a + n) fun y hy => Or.inr (by rw [e5]; omega)).readBytes
        (fun j hj => ⟨by omega, by omega⟩),
      storeMem_read_ne (by rw [eC8]; omega)]
  have hMAt : ShaMainAll b t1.m.memory := hMA.keepW hb (hKK.mono fun a ha => Or.inl (by rw [I]; exact ha.1))
  have rbp1 : t1.m.core.read .rbp = sp - 8#64 := by
    rw [hab.calleeSaved .rbp (by decide), callEntry_read _ _ _ (by decide)]; exact bp5
  have rip1 : t1.m.core.rip = b + 0x36de#64 := by rw [hab.pc, Silmaril.Elf.Link.Dyn.Hello.retOf_of hpr]
  have hdl : loadN t1.m.memory (t1.m.core.read .rbp + 0xffffffffffffff38#64) 1 =
      some (((v4.m.core.read .rdx).setWidth 8).setWidth 64) := by
    rw [rbp1]
    have h1 : t1.m.memory.readBytes (sp - 8#64 + 0xffffffffffffff38#64).toNat 1 =
        (storeMem x.m.memory (sp - 8#64 + 0xffffffffffffff38#64) 1
          (((v4.m.core.read .rdx).setWidth 8).setWidth 64)).readBytes (sp - 8#64 + 0xffffffffffffff38#64).toNat 1 := by
      rw [hk1.readBytes (fun j hj => Or.inr (by rw [csp, eC8]; omega)), cm,
        (pushMem_keeps (P := fun y => y = sp.toNat - 208) fun y hy => Or.inr (by rw [e5]; omega)).readBytes
          (fun j hj => by rw [eC8]; omega)]
    have h2 := loadN_store1 (m := x.m.memory) (v := ((v4.m.core.read .rdx).setWidth 8).setWidth 64) hrC8
    rw [sw_c] at h2
    simp only [loadN] at h2 ⊢
    rw [h1]; exact h2
  refine step36de I hb gd hMAt rip1 hax hdl ?_
  intro v6 r6 m6 g6 R6 d6 f6
  have hd6 : v6.g.done = none := by rw [g6]; exact gd
  have rbp6 : v6.m.core.read .rbp = sp - 8#64 := by rw [R6 _ (by decide) (by decide)]; exact rbp1
  have fs6 : v6.m.core.fsBase = x.m.core.fsBase := by
    rw [f6, hfs]; show v5.m.core.fsBase = _; rw [f5, f4, f3, f2, f1]
  refine step2d08 I hb hd6 (m6 ▸ hMAt) r6 ?_ (g := g) ?_ ?_ ?_
  · rw [d6, sw_a, sw_b, sw_b]; exact dl4
  · rw [m6, rbp6]
    have e : (sp - 8#64 + 0xffffffffffffffc8#64).toNat = sp.toNat - 64 :=
      (fp_neg sp 0x38 (by omega) (by decide) (by decide)).trans (by omega)
    refine loadN_enc ?_
    rw [e]
    rw [hread _ _ (by omega) (by omega)]; exact hgs
  · rw [m6, fs6, loadN_keeps hKK (fun j hj => hgk j hj)]; exact hg
  intro v7 r7 m7 g7 R7 a7 f7
  have hd7 : v7.g.done = none := by rw [g7]; exact hd6
  have rbp7 : v7.m.core.read .rbp = sp - 8#64 := by rw [R7 _ (by decide) (by decide)]; exact rbp6
  have hm7 : v7.m.memory = t1.m.memory := m7.trans m6
  have hsv := hB.saved
  simp only [sv6, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, hspB] at hsv
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := hsv
  have ad : ∀ k, 8 + k ≤ sp.toNat → 0 < k → k < 2 ^ 64 →
      (sp - 8#64 + BitVec.ofNat 64 (2 ^ 64 - k)).toNat = sp.toNat - 8 - k := fun k h1 h2 h3 => fp_neg sp k h1 h2 h3
  refine step2d21 I hb hd7 (hm7 ▸ hMAt) r7 (w1 := sB.m.core.read .rbx) (w2 := sB.m.core.read .r12)
    (w3 := sB.m.core.read .r13) (w4 := sB.m.core.read .r14) (w5 := sB.m.core.read .r15) (w6 := sB.m.core.read .rbp)
    (w7 := R) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hm7, rbp7, show (sp - 8#64 + 0xffffffffffffffd8#64).toNat = sp.toNat - 48 from (ad 0x28 (by omega) (by decide) (by decide)).trans (by omega),
      hread _ _ (by omega) (by omega)]; exact word_rb s6
  · rw [hm7, rbp7, show (sp - 8#64 + 0xffffffffffffffe0#64).toNat = sp.toNat - 40 from (ad 0x20 (by omega) (by decide) (by decide)).trans (by omega),
      hread _ _ (by omega) (by omega)]; exact word_rb s5
  · rw [hm7, rbp7, show (sp - 8#64 + 0xffffffffffffffe8#64).toNat = sp.toNat - 32 from (ad 0x18 (by omega) (by decide) (by decide)).trans (by omega),
      hread _ _ (by omega) (by omega)]; exact word_rb s4
  · rw [hm7, rbp7, show (sp - 8#64 + 0xfffffffffffffff0#64).toNat = sp.toNat - 24 from (ad 0x10 (by omega) (by decide) (by decide)).trans (by omega),
      hread _ _ (by omega) (by omega)]; exact word_rb s3
  · rw [hm7, rbp7, show (sp - 8#64 + 0xfffffffffffffff8#64).toNat = sp.toNat - 16 from (ad 0x8 (by omega) (by decide) (by decide)).trans (by omega),
      hread _ _ (by omega) (by omega)]; exact word_rb s2
  · rw [hm7, rbp7, BitVec.add_zero, e8, hread _ _ (by omega) (by omega)]; exact word_rb s1
  · rw [hm7, rbp7, BitVec.sub_add_cancel, hread _ _ (by omega) (by omega)]; exact word_rb hret
  intro w8 r8 m8 g8 _ R8 f8
  refine k w8 r8 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [R8 .rax (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact a7
  · rw [g8, g7, g6, go]; show v5.g.out = _; rw [g5, g4, g3, g2, g1]
  · rw [g8, g7, g6, gj]; show v5.g.jobs = _; rw [g5, g4, g3, g2, g1]
  · rw [g8, g7, g6, ga]; show v5.g.atexit = _; rw [g5, g4, g3, g2, g1]
  · rw [g8, g7, g6]; exact gd
  · rw [m8, hm7]; exact hKK
  · intro f st' hne hf
    rw [m8, hm7]; exact hOK f st' (by rw [hrdi]; exact hne) (hfile _ _ hf)
  · rw [f8, f7]; exact fs6

end Silmaril.Elf.Link.Dyn.Sha256sum
