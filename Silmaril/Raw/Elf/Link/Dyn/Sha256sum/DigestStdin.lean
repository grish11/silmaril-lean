module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.DigestFile
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MemMain

/-! # GNU `sha256sum`: `digest_file ("-")`, standard input

The name `-`: `r14 = 0` (`sha_digest_mid_dash`); `have_read_stdin = true`; the stream is
libc's `stdin`; then the code shared with a named file from `0x6baf` (`dg_setup`, `dg_init`, the
read loop, `dg_flush`, `dg_final`); at the end `clearerr_unlocked (stdin)` instead of `rpl_fclose`.
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
open Silmaril.Elf.Link.Dyn.Imports
open Silmaril.Elf.Link.Dyn.Hello (abiEntry_of retOf_of)

@[simp] theorem st_write_read (c : State) (r r' : Reg) (v : Word) :
    (c.write r v).read r' = c.regs.write r v r' := rfl

/-- `movzx r32, byte [src + d]`. -/
theorem exec_movzxbd (dst src : Reg) (d : BitVec 32) (c : State) (m : Memory) (l : Nat) (v : Word)
    (h : loadN m (c.read src + d.signExtend 64) 1 = some v) :
    Silmaril.X86.Ext9.exec (.ext8 (.base (.movx false .d .b dst (.mem (Silmaril.X86.Ext.Mem.ofReg src Option.none d)))))
      c m l = .ok { Silmaril.X86.Ext.Sz.d.write c dst ((v.setWidth 8).setWidth 32) with
        rip := c.rip + BitVec.ofNat 64 l } m := by
  simp [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire,
    Silmaril.X86.Ext.readNarrow, ofReg_addr, h, Silmaril.X86.Ext.Narrow.bytes, Silmaril.X86.Ext.Narrow.bits]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- **`digest_file ("-")` from its prologue to `*missing = false`** (`0x6a57`–`0x6a88`, standard input): the frame slots
(file name, result pointer, stack guard) and `*missing = 0`. -/
theorem sha_digest_mid_dash {E : Env} {R : ShaRep} {W : World} {b lb kb : Word} (I : DigImps E R W b lb kb)
    {Q : PState → Prop} {s u : PState} (hP : DigPro W b lb kb s u) (hlo : E.S.lo + 1024 ≤ (s.m.core.read .rsp).toNat)
    (hpk : ∀ j, j < 2 → W.Kept ((s.m.core.read .rdi).toNat + j))
    {c0 : Byte} (hc0 : s.m.memory.readBytes (s.m.core.read .rdi).toNat 1 = some [c0]) (hc0' : c0 = 0x2d#8)
    (hc1' : s.m.memory.readBytes ((s.m.core.read .rdi).toNat + 1) 1 = some [0#8])
    (hb2 : (s.m.core.read .rdi).toNat + 1 < 2 ^ 64)
    (hX : ∀ a, DX s a → ¬ W.Kept a ∧ (s.m.core.read .rsp).toNat + 8 ≤ a)
    (hmiss : s.m.memory.Permitted .write (s.m.core.read .rdx).toNat 1)
    (hmissr : s.m.memory.Permitted .read (s.m.core.read .rdx).toNat 1)
    {g : Word} (hg : loadN s.m.memory (s.m.core.fsBase + 0x28#64) 8 = some g)
    (hgk : ∀ j, j < 8 → W.Kept ((s.m.core.fsBase + 0x28#64).toNat + j))
    (k : ∀ x, DigMid E W b lb kb s x g → x.m.core.rip = b + 0x6a88#64 →
      BitVec.setWidth 32 (x.m.core.read .r14) = 0#32 → MustQ W Q x) :
    MustQ W Q u := by
  have hin : ∀ n, n < 0xa188 → W.InImage (b + BitVec.ofNat 64 n).toNat := fun n hn => sha_in' I.cl.img I.cl.hb hn
  have hB := hP.body
  have hroom := hB.room
  have hsp := hroom.1
  have hsp2 := hroom.2.1
  have hMk := shaMemCD_keep (lb := lb) (kb := kb) I.cl.img I.cl.hb
  have e8 : (s.m.core.read .rsp - 8#64).toNat = (s.m.core.read .rsp).toNat - 8 :=
    sub_toNat (k := 8) (by omega) (by decide)
  -- the three frame slots
  have a1 : (u.m.core.read .rbp + BitVec.signExtend 64 0xffffff38#32).toNat = (s.m.core.read .rsp).toNat - 208 := by
    rw [hP.rbp, show BitVec.signExtend 64 0xffffff38#32 = 0xffffffffffffff38#64 by decide, BitVec.toNat_add, e8]
    simp only [BitVec.toNat_ofNat]; omega
  have pw1 : u.m.memory.Permitted .write (u.m.core.read .rbp + BitVec.signExtend 64 0xffffff38#32).toNat 8 := by
    rw [a1]; exact room_perm hroom (Or.inr rfl) (by omega) (by omega)
  -- the memory as of `s` below the frame and above it (the path, the guard)
  have hkS : Keeps (fun a => a < (s.m.core.read .rsp).toNat - 1024 ∨ (s.m.core.read .rsp).toNat + 8 ≤ a)
      s.m.memory u.m.memory := fun a ha => ⟨hP.low a (by omega), fun acc => by simp only [Memory.permits, hP.regs]⟩
  have hKout : ∀ a, W.Kept a → a < (s.m.core.read .rsp).toNat - 1024 ∨ (s.m.core.read .rsp).toNat + 8 ≤ a := by
    intro a ha
    by_contra hc
    exact (hroom.2.2 a (by omega) (by omega)).2.2 ha
  set A1 := u.m.core.read .rbp + BitVec.signExtend 64 0xffffff38#32 with hA1
  have hk1 : Keeps (fun a => a < (s.m.core.read .rsp).toNat - 208 ∨ (s.m.core.read .rsp).toNat - 200 ≤ a)
      u.m.memory (storeMem u.m.memory A1 8 (u.m.core.read .rdi)) := storeMem_keeps fun x hx => by rw [a1]; omega
  have hc1 : (storeMem u.m.memory A1 8 (u.m.core.read .rdi)).readBytes (u.m.core.read .rdi).toNat 1 = some [c0] := by
    rw [hk1.readBytes (fun j hj => by rw [hP.rdi]; have := hKout _ (hpk 0 (by omega)); omega),
      hkS.readBytes (fun j hj => by rw [hP.rdi]; have := hKout _ (hpk 0 (by omega)); omega), hP.rdi]
    exact hc0
  refine must_listed (o := 23) shaD_listing_ok.2.2 rfl hB.done (by rw [hP.rip]; exact hin _ (by decide))
    hB.mem.2.digestFile (by rw [hP.rip, ripadd]) ?_
  rw [exec_storeq _ _ _ _ _ _ pw1, WP_ok]
  refine must_listed (o := 30) shaD_listing_ok.2.2 rfl hB.done (by simp only [hP.rip, ripadd]; exact hin _ (by decide))
    (hMk _ _ hB.mem (hk1.mono fun x hx => by have := hKout x (Or.inl hx); omega)).2.digestFile
    (by simp only [hP.rip, ripadd]) ?_
  rw [exec_movzxb _ _ _ _ _ (BitVec.ofNat 64 c0.toNat) (by exact loadN_one hc1), WP_ok]
  -- an opaque state again
  refine must_gen (fun v => v.m.core.rip = b + 0x6a62#64 ∧ v.m.memory = storeMem u.m.memory A1 8 (u.m.core.read .rdi) ∧
      v.m.core.read .rbp = u.m.core.read .rbp ∧ v.m.core.read .r12 = u.m.core.read .r12 ∧
      v.m.core.read .rsi = u.m.core.read .rsi ∧ v.m.core.read .rsp = u.m.core.read .rsp ∧
      v.m.core.read .rdi = u.m.core.read .rdi ∧
      BitVec.setWidth 32 (v.m.core.read .r14) = ((BitVec.ofNat 64 c0.toNat).setWidth 8).setWidth 32 ∧
      v.m.core.fsBase = u.m.core.fsBase ∧ v.g = u.g ∧
      (∀ r ∈ Silmaril.X86.sysv64.calleeSaved, r ≠ .r14 → v.m.core.read r = u.m.core.read r)) ?_ ?_
  · refine ⟨by simp [hP.rip, ripadd], rfl, by simp [Silmaril.X86.Ext.Sz.write], by simp [Silmaril.X86.Ext.Sz.write],
      by simp [Silmaril.X86.Ext.Sz.write], by simp [Silmaril.X86.Ext.Sz.write], by simp [Silmaril.X86.Ext.Sz.write],
      ?_, rfl, rfl, ?_⟩
    · simp [Silmaril.X86.Ext.Sz.write]
    · intro r hr hne
      simp only [Silmaril.X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | exact absurd rfl hne | simp [Silmaril.X86.Ext.Sz.write]
  rintro v ⟨hrv, hmv, hbpv, h12v, hsiv, hspv, hdiv, h14v, hfsv, hgv, hcsv⟩
  have hmv' : ShaMemCD b lb kb v.m.memory := by
    rw [hmv]; exact hMk _ _ hB.mem (hk1.mono fun x hx => by have := hKout x (Or.inl hx); omega)
  have a2 : (v.m.core.read .rbp + BitVec.signExtend 64 0xffffff40#32).toNat = (s.m.core.read .rsp).toNat - 200 := by
    rw [hbpv, hP.rbp, show BitVec.signExtend 64 0xffffff40#32 = 0xffffffffffffff40#64 by decide, BitVec.toNat_add, e8]
    simp only [BitVec.toNat_ofNat]; omega
  have pw2 : v.m.memory.Permitted .write (v.m.core.read .rbp + BitVec.signExtend 64 0xffffff40#32).toNat 8 := by
    rw [a2, hmv, storeMem_permitted]; exact room_perm hroom (Or.inr rfl) (by omega) (by omega)
  refine must_listed (o := 34) shaD_listing_ok.2.2 rfl (by rw [hgv]; exact hB.done) (by rw [hrv]; exact hin _ (by decide))
    hmv'.2.digestFile (by rw [hrv, ripadd]) ?_
  rw [exec_storeq _ _ _ _ _ _ pw2, WP_ok]
  have hk2 : Keeps (fun a => a < (s.m.core.read .rsp).toNat - 208 ∨ (s.m.core.read .rsp).toNat - 192 ≤ a)
      u.m.memory (storeMem v.m.memory (v.m.core.read .rbp + BitVec.signExtend 64 0xffffff40#32) 8 (v.m.core.read .rsi)) := by
    rw [hmv]
    exact (hk1.mono fun x hx => by omega).trans (storeMem_keeps fun x hx => by rw [a2]; omega)
  have hgk' : ∀ j, j < 8 → (s.m.core.fsBase + 0x28#64).toNat + j < (s.m.core.read .rsp).toNat - 1024 ∨
      (s.m.core.read .rsp).toNat + 8 ≤ (s.m.core.fsBase + 0x28#64).toNat + j := fun j hj => hKout _ (hgk j hj)
  have hgv2 : loadN (storeMem v.m.memory (v.m.core.read .rbp + BitVec.signExtend 64 0xffffff40#32) 8 (v.m.core.read .rsi))
      (v.m.core.fsBase + BitVec.signExtend 64 0x28#32) 8 = some g := by
    rw [hfsv, hB.fs, show BitVec.signExtend 64 0x28#32 = 0x28#64 by decide,
      hk2.loadN (fun j hj => by have := hgk' j hj; omega), hkS.loadN (fun j hj => hgk' j hj)]
    exact hg
  refine must_listed (o := 41) shaD_listing_ok.2.2 rfl (by rw [hgv]; exact hB.done) (by simp only [hrv, ripadd]; exact hin _ (by decide))
    (hMk _ _ hB.mem (hk2.mono fun x hx => by have := hKout x (Or.inl hx); omega)).2.digestFile (by simp only [hrv, ripadd]) ?_
  rw [exec_loadfs _ _ _ _ _ _ (by exact hgv2), WP_ok]
  refine must_gen (fun w => w.m.core.rip = b + 0x6a72#64 ∧
      w.m.memory = storeMem v.m.memory (v.m.core.read .rbp + BitVec.signExtend 64 0xffffff40#32) 8 (v.m.core.read .rsi) ∧
      w.m.core.read .rax = g ∧
      w.m.core.read .rbp = u.m.core.read .rbp ∧ w.m.core.read .r12 = u.m.core.read .r12 ∧
      w.m.core.read .rsi = u.m.core.read .rsi ∧ w.m.core.read .rsp = u.m.core.read .rsp ∧
      w.m.core.read .rdi = u.m.core.read .rdi ∧
      BitVec.setWidth 32 (w.m.core.read .r14) = ((BitVec.ofNat 64 c0.toNat).setWidth 8).setWidth 32 ∧
      w.m.core.fsBase = u.m.core.fsBase ∧ w.g = u.g ∧
      (∀ r ∈ Silmaril.X86.sysv64.calleeSaved, r ≠ .r14 → w.m.core.read r = u.m.core.read r)) ?_ ?_
  · refine ⟨by simp [hrv, ripadd], rfl, by simp, by simp [hbpv], by simp [h12v], by simp [hsiv], by simp [hspv], by simp [hdiv],
      by simpa using h14v, by simp [hfsv], hgv, ?_⟩
    intro r hr hne
    have hh := hcsv r hr hne
    simp only [Silmaril.X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact absurd rfl hne | simp [hh]
  rintro w ⟨hrw, hmw, haxw, hbpw, h12w, hsiw, hspw, hrdiw, h14w, hfsw, hgw, hcsw⟩
  have a3 : (w.m.core.read .rbp + BitVec.signExtend 64 0xffffffc8#32).toNat = (s.m.core.read .rsp).toNat - 64 := by
    rw [hbpw, hP.rbp, show BitVec.signExtend 64 0xffffffc8#32 = 0xffffffffffffffc8#64 by decide, BitVec.toNat_add, e8]
    simp only [BitVec.toNat_ofNat]; omega
  have pw3 : w.m.memory.Permitted .write (w.m.core.read .rbp + BitVec.signExtend 64 0xffffffc8#32).toNat 8 := by
    rw [a3, hmw, storeMem_permitted, hmv, storeMem_permitted]; exact room_perm hroom (Or.inr rfl) (by omega) (by omega)
  have hmw' : ShaMemCD b lb kb w.m.memory := by
    rw [hmw]; exact hMk _ _ hB.mem (hk2.mono fun x hx => by have := hKout x (Or.inl hx); omega)
  refine must_listed (o := 50) shaD_listing_ok.2.2 rfl (by rw [hgw]; exact hB.done) (by rw [hrw]; exact hin _ (by decide))
    hmw'.2.digestFile (by rw [hrw, ripadd]) ?_
  rw [exec_storeq _ _ _ _ _ _ pw3, WP_ok]
  have a3' : (w.m.core.read .rbp + 18446744073709551560#64).toNat = (s.m.core.read .rsp).toNat - 64 := a3
  have hx14 : BitVec.setWidth 32 (w.m.core.read .r14) = 45#32 := by
    rw [h14w, hc0']; decide
  have hne1 : Silmaril.X86.Ext.Cond.eval (subD (BitVec.setWidth 32 (w.m.core.read .r14)) 45#32) .ne = some false := by
    rw [eval_subD]; simp [Silmaril.X86.Ext.Cond.afterCmp, hx14]
  have hne2 : Silmaril.X86.Ext.Cond.eval (@Silmaril.X86.Ext.AluOp.flagsN 32 Silmaril.X86.AluOp.sub
      (BitVec.setWidth 32 (w.m.core.read .r14)) 45#32) .ne = some false := hne1
  refine must_listed (o := 54) shaD_listing_ok.2.2 rfl (by rw [hgw]; exact hB.done) (by simp only [hrw, ripadd]; exact hin _ (by decide))
    (hMk _ _ hmw' (storeMem_keeps fun x hx => by
      rw [a3]; have := hKout x (Or.inl hx); omega)).2.digestFile (by simp only [hrw, ripadd]) ?_
  xstep [hrw]
  refine must_listed (o := 56) shaD_listing_ok.2.2 rfl (by rw [hgw]; exact hB.done) (hin _ (by decide))
    (hMk _ _ hmw' (storeMem_keeps fun x hx => by
      rw [a3']; have := hKout x (Or.inl hx); omega)).2.digestFile (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 60) shaD_listing_ok.2.2 rfl (by rw [hgw]; exact hB.done) (hin _ (by decide))
    (hMk _ _ hmw' (storeMem_keeps fun x hx => by
      rw [a3']; have := hKout x (Or.inl hx); omega)).2.digestFile (by rw [ripadd]) ?_
  xstep [hne1, hne2]
  -- the second byte of the name (its terminating NUL)
  have hc1w : loadN (storeMem w.m.memory (w.m.core.read .rbp + 18446744073709551560#64) 8 (w.m.core.read .rax))
      (w.m.core.read .rdi + BitVec.signExtend 64 1#32) 1 = some (BitVec.ofNat 64 (0#8 : Byte).toNat) := by
    have hrdi : (w.m.core.read .rdi + BitVec.signExtend 64 1#32).toNat = (s.m.core.read .rdi).toNat + 1 := by
      have hw := hrdiw
      rw [hw, hP.rdi, show BitVec.signExtend 64 1#32 = 1#64 by decide, BitVec.toNat_add]
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega)]
    apply loadN_one
    rw [hrdi, storeMem_read_ne (by have := a3'; have := hKout _ (hpk 1 (by omega)); omega), hmw,
      hk2.readBytes (fun j hj => by have := hKout _ (hpk 1 (by omega)); omega),
      hkS.readBytes (fun j hj => by have := hKout _ (hpk 1 (by omega)); omega)]
    exact hc1'
  refine must_listed (o := 62) shaD_listing_ok.2.2 rfl (by rw [hgw]; exact hB.done) (hin _ (by decide))
    (hMk _ _ hmw' (storeMem_keeps fun x hx => by
      rw [a3']; have := hKout x (Or.inl hx); omega)).2.digestFile (by rw [ripadd]) ?_
  rw [exec_movzxbd _ _ _ _ _ _ _ (by
    simpa only [st_read_mk, Silmaril.Machine.RegisterFile.write_other, ne_eq, reduceCtorEq, not_false_eq_true,
      st_write_read, st_regs_apply] using hc1w), WP_ok]
  -- `*missing = false`
  have hregs : ∀ acc a len, (storeMem w.m.memory (w.m.core.read .rbp + 18446744073709551560#64) 8
      (w.m.core.read .rax)).Permitted acc a len ↔ s.m.memory.Permitted acc a len := by
    intro acc a len
    rw [storeMem_permitted, hmw, storeMem_permitted, hmv, storeMem_permitted]
    simp only [Memory.Permitted, Memory.checkSpan, Memory.permits, hP.regs]
  refine must_listed (o := 67) shaD_listing_ok.2.2 rfl (by rw [hgw]; exact hB.done)
    (by simp only [ripadd]; exact hin _ (by decide))
    (hMk _ _ hmw' (storeMem_keeps fun x hx => by
      rw [a3']; have := hKout x (Or.inl hx); omega)).2.digestFile (by simp only [ripadd]) ?_
  rw [exec_storeb _ _ _ _ _ (by
    simp only [st_read_mk, Silmaril.Machine.RegisterFile.write_other, ne_eq, reduceCtorEq, not_false_eq_true,
      st_write_read, st_regs_apply, Silmaril.X86.Ext.Sz.write]
    rw [hregs, h12w, hP.r12]; exact hmiss), WP_ok]
  -- the frame after the four stores
  have hsv := sv6_bound s
  have hsvb : ∀ q ∈ sv6 s, q.1 ≤ 48 := fun q hq => (hsv q hq).1
  have hA1 : A1.toNat = (s.m.core.read .rsp).toNat - 208 := a1
  let st1 : PState := ⟨⟨u.m.core, storeMem u.m.memory A1 8 (u.m.core.read .rdi)⟩, u.g⟩
  have hB1 : BodyX W (ShaMemCD b lb kb) s st1 216 1024 (sv6 s) (MX s) :=
    BodyX.store hMk hB (by decide) hsvb (by rw [hA1]; omega) (by rw [hA1]; omega) rfl rfl rfl rfl
  have hB2 : BodyX W (ShaMemCD b lb kb) s w 216 1024 (sv6 s) (MX s) :=
    BodyX.store hMk hB1 (by decide) hsvb (a := v.m.core.read .rbp + BitVec.signExtend 64 0xffffff40#32)
      (v := v.m.core.read .rsi) (k := 8) (by rw [a2]; omega) (by rw [a2]; omega) (by rw [hmw, hmv])
      (by rw [hspw]) (by rw [hfsw]) (by rw [hgw])
  let st3 : PState := ⟨⟨w.m.core, storeMem w.m.memory (w.m.core.read .rbp + 18446744073709551560#64) 8
    (w.m.core.read .rax)⟩, w.g⟩
  have hB3 : BodyX W (ShaMemCD b lb kb) s st3 216 1024 (sv6 s) (MX s) :=
    BodyX.store hMk hB2 (by decide) hsvb (by rw [a3']; omega) (by rw [a3']; omega) rfl rfl rfl rfl
  have hB4 : BodyX W (ShaMemCD b lb kb) s ⟨⟨w.m.core, storeMem st3.m.memory (s.m.core.read .rdx) 1
      (BitVec.setWidth 64 0#8)⟩, w.g⟩ 216 1024 (sv6 s) (MX s) :=
    BodyX.storeX hMk hB3 (sv6_bound8 s) (fun x h1 h2 => by
      have hd : DX s x := Or.inl ⟨h1, h2⟩
      exact ⟨⟨h1, h2⟩, (hX x hd).1, Or.inr (hX x hd).2⟩) rfl rfl rfl rfl
  have hr12 : w.m.core.read .r12 = s.m.core.read .rdx := by rw [h12w, hP.r12]
  -- reading back the slots
  have hrA1 : u.m.memory.Permitted .read A1.toNat 8 := by rw [hA1]; exact room_perm hroom (Or.inl rfl) (by omega) (by omega)
  have hrA2 : v.m.memory.Permitted .read (v.m.core.read .rbp + BitVec.signExtend 64 0xffffff40#32).toNat 8 := by
    rw [a2, hmv, storeMem_permitted]; exact room_perm hroom (Or.inl rfl) (by omega) (by omega)
  have hrA3 : w.m.memory.Permitted .read (w.m.core.read .rbp + 18446744073709551560#64).toNat 8 := by
    rw [a3', hmw, storeMem_permitted, hmv, storeMem_permitted]; exact room_perm hroom (Or.inl rfl) (by omega) (by omega)
  have kM4 : ∀ {P : Nat → Prop}, (∀ x, P x → x < (s.m.core.read .rdx).toNat ∨ (s.m.core.read .rdx).toNat + 1 ≤ x) →
      Keeps P st3.m.memory (storeMem st3.m.memory (s.m.core.read .rdx) 1 (BitVec.setWidth 64 0#8)) :=
    fun hP => storeMem_keeps hP
  have hrdx : (s.m.core.read .rsp).toNat + 8 ≤ (s.m.core.read .rdx).toNat :=
    (hX _ (Or.inl ⟨le_refl _, by omega⟩)).2
  refine must_gen (fun x => DigMid E W b lb kb s x g ∧ x.m.core.rip = b + 0x6a88#64 ∧
      BitVec.setWidth 32 (x.m.core.read .r14) = 0#32) ?_ ?_
  · refine ⟨⟨hB4.of_eq (by simp [Silmaril.X86.Ext.Sz.write, st3, hr12])
      (by simp [Silmaril.X86.Ext.Sz.write, hspw, hB.rsp]) (by simp [Silmaril.X86.Ext.Sz.write, hfsw]) (by simp [hgw]),
      by simp [Silmaril.X86.Ext.Sz.write, hbpw, hP.rbp], by simp [Silmaril.X86.Ext.Sz.write, hr12], ?_, ?_, ?_, ?_, ?_,
      by simp [hgw, hP.g], by simp only [storeMem]; rw [hmw, hmv]; simp only [storeMem]; exact hP.regs⟩,
      by simp [ripadd], ?_⟩
    · show (storeMem _ _ 1 _).readBytes _ 8 = _
      rw [storeMem_read_ne (by simp only [Silmaril.X86.Ext.Sz.write, st_read_mk, Silmaril.Machine.RegisterFile.write_other, ne_eq, reduceCtorEq,
          not_false_eq_true, st_write_read, st_regs_apply, hr12]; omega),
        storeMem_read_ne (by rw [a3']; omega), hmw, storeMem_read_ne (by rw [a2]; omega), hmv, ← hA1]
      rw [storeMem_read8 hrA1, hP.rdi]
    · show (storeMem _ _ 1 _).readBytes _ 8 = _
      rw [storeMem_read_ne (by simp only [Silmaril.X86.Ext.Sz.write, st_read_mk, Silmaril.Machine.RegisterFile.write_other, ne_eq, reduceCtorEq,
          not_false_eq_true, st_write_read, st_regs_apply, hr12]; omega),
        storeMem_read_ne (by rw [a3']; omega), hmw, ← a2]
      rw [storeMem_read8 hrA2, hsiv, hP.rsi]
    · show (storeMem _ _ 1 _).readBytes _ 8 = _
      rw [storeMem_read_ne (by simp only [Silmaril.X86.Ext.Sz.write, st_read_mk, Silmaril.Machine.RegisterFile.write_other, ne_eq, reduceCtorEq,
          not_false_eq_true, st_write_read, st_regs_apply, hr12]; omega),
        ← a3']
      rw [storeMem_read8 hrA3, haxw]
    · show (storeMem _ _ 1 _).readBytes _ 1 = _
      simp only [Silmaril.X86.Ext.Sz.write, st_read_mk, Silmaril.Machine.RegisterFile.write_other, ne_eq, reduceCtorEq,
        not_false_eq_true, st_write_read, st_regs_apply, hr12]
      rw [storeMem_read (by
        rw [storeMem_permitted, hmw, storeMem_permitted, hmv, storeMem_permitted]
        simp only [Memory.Permitted, Memory.checkSpan, Memory.permits, hP.regs]
        exact hmissr)]
      rfl
    · intro a ha
      have hk : Keeps (fun x => x < E.S.lo) s.m.memory
          (storeMem (storeMem w.m.memory (w.m.core.read .rbp + 18446744073709551560#64) 8 (w.m.core.read .rax))
            (s.m.core.read .rdx) 1 (BitVec.setWidth 64 0#8)) := by
        have h2 : Keeps (fun x => x < E.S.lo) s.m.memory w.m.memory := by
          rw [hmw]; exact (hkS.mono fun x hx => by omega).trans (hk2.mono fun x hx => by omega)
        exact (h2.trans (storeMem_keeps fun x hx => by rw [a3']; omega)).trans (storeMem_keeps fun x hx => by omega)
      have := hk a ha
      simp only [Silmaril.X86.Ext.Sz.write, st_read_mk, Silmaril.Machine.RegisterFile.write_other, ne_eq, reduceCtorEq,
        not_false_eq_true, st_write_read, st_regs_apply, hr12]
      exact ⟨this.1, this.2⟩
    · simp [Silmaril.X86.Ext.Sz.write]
  rintro x ⟨hM, hrx, h14x⟩
  exact k x hM hrx h14x


/-- `mov rN, [rip + d]` (64-bit). -/
theorem exec_loadq_ripD (dst : Reg) (d : BitVec 32) (c : State) (m : Memory) (l : Nat) (v : Word)
    (h : loadN m (c.rip + BitVec.ofNat 64 l + d.signExtend 64) 8 = some v) :
    Silmaril.X86.Ext9.exec (.ext8 (.base (.load .q dst (Silmaril.X86.Ext.Mem.ofRip d)))) c m l =
      .ok { c.write dst v with rip := c.rip + BitVec.ofNat 64 l } m := by
  simp [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire,
    Silmaril.X86.Ext.readRM, ofRip_addr, h, Silmaril.X86.Ext.Sz.bytes, Silmaril.X86.Ext.Sz.write]

/-- `mov byte [rip + d], imm8`. -/
theorem exec_storeb_rip (d : BitVec 32) (imm : BitVec 8) (c : State) (m : Memory) (l : Nat)
    (h : m.Permitted .write (c.rip + BitVec.ofNat 64 l + d.signExtend 64).toNat 1) :
    Silmaril.X86.Ext9.exec (.ext8 (.base (.movI8 (.mem (Silmaril.X86.Ext.Mem.ofRip d)) imm))) c m l =
      .ok { c with rip := c.rip + BitVec.ofNat 64 l }
        (storeMem m (c.rip + BitVec.ofNat 64 l + d.signExtend 64) 1 (imm.setWidth 64)) := by
  simp [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire,
    Silmaril.X86.Ext.writeRM8, ofRip_addr, storeN_ok h]

/-- `have_read_stdin` (`.bss`, one byte). -/
def HR (b : Word) (a : Nat) : Prop := a = (b + 0xa160#64).toNat

/-- A store into the program's own writable data (outside the image facts the code needs). -/
theorem BodyX.storeImg {W : World} {b lb kb : Word} (hb : b.toNat + 0xa188 < 2 ^ 64)
    {s u u' : PState} {fr n : Nat} {saved : List (Nat × Word)} {X : Nat → Prop}
    (hB : BodyX W (ShaMemCD b lb kb) s u fr n saved X) (hsv8 : ∀ p ∈ saved, 8 ≤ p.1 ∧ p.1 ≤ n) {a v : Word} {k : Nat}
    (ha : ∀ x, a.toNat ≤ x → x < a.toNat + k → X x ∧ ¬ ImgW b x ∧
      (x + n < (s.m.core.read .rsp).toNat ∨ (s.m.core.read .rsp).toNat + 8 ≤ x))
    (hm : u'.m.memory = storeMem u.m.memory a k v) (hr : u'.m.core.read .rsp = u.m.core.read .rsp)
    (hf : u'.m.core.fsBase = u.m.core.fsBase) (hd : u'.g.done = u.g.done) :
    BodyX W (ShaMemCD b lb kb) s u' fr n saved X := by
  have hkW : Keeps (ImgW b) u.m.memory (storeMem u.m.memory a k v) := storeMem_keeps fun x hx => by
    by_contra hc
    exact (ha x (by omega) (by omega)).2.1 hx
  refine ⟨hr.trans hB.rsp, ?_, ?_, ?_, hf.trans hB.fs, hd.trans hB.done, ?_, ?_⟩
  · rw [hm]
    exact hB.keepX.trans (storeMem_keeps fun x hx => by
      by_contra hc
      exact hx.2 (ha x (by omega) (by omega)).1)
  · rw [hm]; exact hB.room.keeps fun _ _ _ _ => rfl
  · rw [hm]; exact ⟨ShaMemC.keepW hb hB.mem.1 hkW, ShaMemD.keepW hb hB.mem.2 hkW⟩
  · intro p hp
    rw [hm, (storeMem_keeps (P := fun x => (s.m.core.read .rsp).toNat - n ≤ x ∧ x < (s.m.core.read .rsp).toNat)
      (m := u.m.memory) (a := a) (k := k) (v := v) fun x hx => by
        by_contra hc
        rcases (ha x (by omega) (by omega)).2.2 with h' | h' <;> omega).readBytes (fun j hj => by
          have := hB.room.1; have := (hsv8 p hp).1; have := (hsv8 p hp).2; omega)]
    exact hB.saved p hp
  · intro x h1 h2 acc
    rw [hm]; exact hB.perm x h1 h2 acc

/-- The entry state with `have_read_stdin = 1`: `digest_file ("-")`'s frame is stated relative to it
after the store, so that the byte is kept from there on. -/
def hrBase (b : Word) (s : PState) : PState :=
  ⟨⟨s.m.core, storeMem s.m.memory (b + 0xa160#64) 1 (BitVec.setWidth 64 1#8)⟩, s.g⟩

/-- A store to kept memory outside the frame, made both at the entry state and now. -/
theorem BodyX.rebase {W : World} {b lb kb : Word} (hb : b.toNat + 0xa188 < 2 ^ 64)
    {s u u' : PState} {fr n : Nat} {saved : List (Nat × Word)} {X : Nat → Prop}
    (hB : BodyX W (ShaMemCD b lb kb) s u fr n saved X) (hsv8 : ∀ p ∈ saved, 8 ≤ p.1 ∧ p.1 ≤ n) {a v : Word} {k : Nat}
    (ha : ∀ x, a.toNat ≤ x → x < a.toNat + k → W.Kept x ∧ ¬ X x ∧ ¬ ImgW b x ∧
      (x + n < (s.m.core.read .rsp).toNat ∨ (s.m.core.read .rsp).toNat + 8 ≤ x))
    (hm : u'.m.memory = storeMem u.m.memory a k v) (hr : u'.m.core.read .rsp = u.m.core.read .rsp)
    (hf : u'.m.core.fsBase = u.m.core.fsBase) (hd : u'.g.done = u.g.done) :
    BodyX W (ShaMemCD b lb kb) ⟨⟨s.m.core, storeMem s.m.memory a k v⟩, s.g⟩ u' fr n saved X := by
  have hl : (Silmaril.X86.Ext.leBytes v k).length = k := by simp [Silmaril.X86.Ext.leBytes]
  have hkW : Keeps (ImgW b) u.m.memory (storeMem u.m.memory a k v) := storeMem_keeps fun x hx => by
    by_contra hc
    exact (ha x (by omega) (by omega)).2.2.1 hx
  refine ⟨hr.trans hB.rsp, ?_, ?_, ?_, hf.trans hB.fs, hd.trans hB.done, ?_, ?_⟩
  · rw [hm]
    intro x hx
    by_cases hin : a.toNat ≤ x ∧ x < a.toNat + k
    · refine ⟨?_, fun acc => ?_⟩
      · simp only [storeMem]
        rw [show x = a.toNat + (x - a.toNat) by omega, Memory.install_get _ _ _ _ (by rw [hl]; omega),
          Memory.install_get _ _ _ _ (by rw [hl]; omega)]
      · exact (hB.keepX x ⟨Or.inl (ha x hin.1 hin.2).1, (ha x hin.1 hin.2).2.1⟩).2 acc
    · have h1 := hB.keepX x hx
      refine ⟨?_, fun acc => h1.2 acc⟩
      simp only [storeMem]
      rw [Memory.install_outside _ _ _ _ (by rw [hl]; omega), Memory.install_outside _ _ _ _ (by rw [hl]; omega)]
      exact h1.1
  · rw [hm]; exact hB.room.keeps fun _ _ _ _ => rfl
  · rw [hm]; exact ⟨ShaMemC.keepW hb hB.mem.1 hkW, ShaMemD.keepW hb hB.mem.2 hkW⟩
  · intro p hp
    dsimp only
    rw [hm, (storeMem_keeps (P := fun x => (s.m.core.read .rsp).toNat - n ≤ x ∧ x < (s.m.core.read .rsp).toNat)
      (m := u.m.memory) (a := a) (k := k) (v := v) fun x hx => by
        by_contra hc
        rcases (ha x (by omega) (by omega)).2.2.2 with h' | h' <;> omega).readBytes (fun j hj => by
          have := hB.room.1; have := (hsv8 p hp).1; have := (hsv8 p hp).2; omega)]
    exact hB.saved p hp
  · intro x h1 h2 acc
    rw [hm]; exact hB.perm x h1 h2 acc

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- **`digest_file ("-")` from `*missing = false` to `0x6bb2`**: `have_read_stdin = true`, the
stream is libc's `stdin` (read through the GOT), non-NULL. -/
theorem sha_digest_stdin_head {E : Env} {R : ShaRep} {W : World} {b lb kb : Word} (I : DigImps E R W b lb kb)
    {Q : PState → Prop} {s x : PState} {g Fi : Word} {st : St} (hM : DigMid E W b lb kb s x g)
    (hrx : x.m.core.rip = b + 0x6a88#64) (h14x : BitVec.setWidth 32 (x.m.core.read .r14) = 0#32)
    (hlo : E.S.lo + 1024 ≤ (s.m.core.read .rsp).toNat) (hal : (s.m.core.read .rsp).toNat % 16 = 8)
    (hX : ∀ a, DX s a → ¬ W.Kept a ∧ (s.m.core.read .rsp).toNat + 8 ≤ a)
    (hgot : loadN s.m.memory (b + 0x9fb8#64) 8 = some (lb + 0x2056b0#64))
    (hvar : loadN s.m.memory (lb + 0x2056b0#64) 8 = some Fi)
    (hvark : ∀ j, j < 8 → W.Kept ((lb + 0x2056b0#64).toNat + j))
    (hvarHR : ∀ j, j < 8 → (lb + 0x2056b0#64).toNat + j ≠ (b + 0xa160#64).toNat)
    (hFi : Fi ≠ 0#64)
    (hHRw : s.m.memory.Permitted .write (b + 0xa160#64).toNat 1)
    (hHRp : ¬ E.S.priv s.m.memory (b + 0xa160#64).toNat)
    (hfile : E.S.file s.m.memory Fi st)
    (k : ∀ u, DigFr E W b lb kb (MX s) (hrBase b s) u Fi g 0#32 st → u.m.core.rip = b + 27570#64 →
      u.m.core.read .rdi = Fi → MustQ W Q u) :
    MustQ W Q x := by
  have hin : ∀ n, n < 0xa188 → W.InImage (b + BitVec.ofNat 64 n).toNat := fun n hn => sha_in' I.cl.img I.cl.hb hn
  have hb := I.cl.hb
  have hB := hM.body
  have hroom := hB.room
  have hsp := hroom.1
  have hsp2 := hroom.2.1
  have hKout : ∀ a, W.Kept a → a < (s.m.core.read .rsp).toNat - 1024 ∨ (s.m.core.read .rsp).toNat + 8 ≤ a := by
    intro a ha
    by_contra hc
    exact (hroom.2.2 a (by omega) (by omega)).2.2 ha
  have hbn : ∀ n, n < 0xa188 → (b + BitVec.ofNat 64 n).toNat = b.toNat + n := fun n hn => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega), Nat.mod_eq_of_lt (by omega)]
  have hHRn : (b + 0xa160#64).toNat = b.toNat + 0xa160 := hbn 0xa160 (by decide)
  have hHRk : W.Kept (b + 0xa160#64).toNat := Or.inl (hin 0xa160 (by decide))
  -- what the frame keeps of the entry state (image and stdin variable included)
  have hkK : Keeps (fun a => W.Kept a ∧ ¬ MX s a) s.m.memory x.m.memory :=
    hB.keepX.mono fun a ha => ⟨Or.inl ha.1, ha.2⟩
  have himg : ∀ n, n < 0xa188 → W.Kept (b.toNat + n) := fun n hn => Or.inl (by rw [← hbn n hn]; exact hin n hn)
  have hnotMX : ∀ a, W.Kept a → ¬ MX s a := fun a ha hm => (hX _ (Or.inl hm)).1 ha
  have hgotx : loadN x.m.memory (b + 0x9fb8#64) 8 = some (lb + 0x2056b0#64) := by
    rw [hkK.loadN fun j hj => ⟨by rw [hbn 0x9fb8 (by decide), Nat.add_assoc]; exact himg _ (by omega),
      hnotMX _ (by rw [hbn 0x9fb8 (by decide), Nat.add_assoc]; exact himg _ (by omega))⟩]
    exact hgot
  have hHRwx : x.m.memory.Permitted .write (b + 0xa160#64).toNat 1 := by
    have := hHRw; unfold Memory.Permitted at this ⊢; rw [Memory.checkSpan_iff] at this ⊢
    refine ⟨this.1, this.2.1, fun j hj => ?_⟩
    obtain rfl : j = 0 := by omega
    rw [← this.2.2 0 hj, (hkK _ ⟨by simpa using hHRk, hnotMX _ (by simpa using hHRk)⟩).2]
  have hne : Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.logicFlagsN
      (andD (BitVec.setWidth 32 (x.m.core.read .r14)) (BitVec.setWidth 32 (x.m.core.read .r14)))) .ne = some false := by
    rw [eval_ne_testD]; simp [h14x]
  refine must_listed (o := 72) shaD_listing_ok.2.2 rfl hB.done (by rw [hrx]; exact hin _ (by decide))
    hB.mem.2.digestFile (by rw [hrx, ripadd]) ?_
  xstep [hrx]
  refine must_listed (o := 75) shaD_listing_ok.2.2 rfl hB.done (hin _ (by decide)) hB.mem.2.digestFile (by rw [ripadd]) ?_
  xstep [hne]
  refine must_listed (o := 81) shaD_listing_ok.2.2 rfl hB.done (hin _ (by decide)) hB.mem.2.digestFile (by rw [ripadd]) ?_
  rw [exec_loadq_ripD _ _ _ _ _ (lb + 0x2056b0#64) (by
    show loadN x.m.memory (b + 27281#64 + BitVec.ofNat 64 7 + BitVec.signExtend 64 0x3520#32) 8 = _
    rw [show b + 27281#64 + BitVec.ofNat 64 7 + BitVec.signExtend 64 0x3520#32 = b + 0x9fb8#64 by
      simp only [BitVec.add_assoc]; rfl]
    exact hgotx), WP_ok]
  refine must_listed (o := 88) shaD_listing_ok.2.2 rfl hB.done (by simp only [ripadd]; exact hin _ (by decide))
    hB.mem.2.digestFile (by simp only [ripadd]) ?_
  have hHRaddr : b + 27281#64 + 7#64 + 7#64 + BitVec.signExtend 64 0x36c1#32 = b + 0xa160#64 := by
    simp only [BitVec.add_assoc]; rfl
  rw [exec_storeb_rip _ _ _ _ _ (by dsimp only; rw [hHRaddr]; exact hHRwx), WP_ok]
  dsimp only
  rw [hHRaddr]
  have hvarx : loadN (storeMem x.m.memory (b + 0xa160#64) 1 (BitVec.setWidth 64 1#8)) (lb + 0x2056b0#64) 8 = some Fi := by
    rw [(storeMem_keeps (P := fun a => ∃ j, j < 8 ∧ a = (lb + 0x2056b0#64).toNat + j) fun a ⟨j, hj, he⟩ => by
      have := hvarHR j hj; omega).loadN fun j hj => ⟨j, hj, rfl⟩,
      hkK.loadN fun j hj => ⟨hvark j hj, hnotMX _ (hvark j hj)⟩]
    exact hvar
  refine must_listed (o := 95) shaD_listing_ok.2.2 rfl hB.done (by simp only [ripadd]; exact hin _ (by decide))
    (ShaMemD.keepW hb hB.mem.2 (storeMem_keeps fun a ha => by
      rw [hHRn]; rcases ha.2 with h | h <;> omega)).digestFile (by simp only [ripadd]) ?_
  rw [exec_loadq _ _ _ _ _ Fi (by
    simp only [st_read_mk, st_write_regs, Silmaril.Machine.RegisterFile.write_same]; exact hvarx), WP_ok]
  have hHRout : (b + 0xa160#64).toNat < (s.m.core.read .rsp).toNat - 1024 ∨
      (s.m.core.read .rsp).toNat + 8 ≤ (b + 0xa160#64).toNat := hKout _ hHRk
  have hrdxne : (s.m.core.read .rdx).toNat ≠ (b + 0xa160#64).toNat := fun h =>
    (hX _ (Or.inl ⟨le_refl _, by omega⟩)).1 (h ▸ hHRk)
  have hrdx : (s.m.core.read .rsp).toNat + 8 ≤ (s.m.core.read .rdx).toNat := (hX _ (Or.inl ⟨le_refl _, by omega⟩)).2
  refine must_gen (fun y => BodyX W (ShaMemCD b lb kb) (hrBase b s) y 216 1024 (sv6 s) (MX s) ∧
      y.m.core.rip = b + 0x6aa2#64 ∧ y.m.memory = storeMem x.m.memory (b + 0xa160#64) 1 (BitVec.setWidth 64 1#8) ∧
      y.g = x.g ∧ y.m.core.read .rbx = Fi ∧
      (∀ r ∈ Silmaril.X86.sysv64.calleeSaved, r ≠ .rbx → y.m.core.read r = x.m.core.read r)) ?_ ?_
  · refine ⟨BodyX.rebase hb hB (sv6_bound8 s) (a := b + 0xa160#64) (k := 1)
      (v := BitVec.setWidth 64 1#8) (fun a h1 h2 => by
        have : a = (b + 0xa160#64).toNat := by omega
        subst this
        exact ⟨hHRk, hnotMX _ hHRk, fun hw => by unfold ImgW at hw; rw [hHRn] at hw; omega,
          by rcases hHRout with h | h <;> omega⟩) rfl (by simp) rfl rfl, by simp, rfl, rfl, by simp, ?_⟩
    intro r hr hne
    simp only [Silmaril.X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact absurd rfl hne | simp
  rintro y ⟨hBy, hry, hmy, hgy, hbxy, hcsy⟩
  have hnz : Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.logicFlagsN (andQ (y.m.core.read .rbx) (y.m.core.read .rbx)))
      .ne = some true := by rw [eval_ne_testQ, hbxy]; simp [hFi]
  refine must_listed (o := 98) shaD_listing_ok.2.2 rfl hBy.done (by rw [hry]; exact hin _ (by decide))
    hBy.mem.2.digestFile (by rw [hry, ripadd]) ?_
  xstep [hry]
  refine must_listed (o := 101) shaD_listing_ok.2.2 rfl hBy.done (hin _ (by decide)) hBy.mem.2.digestFile (by rw [ripadd]) ?_
  xstep [hnz]
  refine must_listed (o := 367) shaD_listing_ok.2.2 rfl hBy.done (hin _ (by decide)) hBy.mem.2.digestFile (by rw [ripadd]) ?_
  xstep []
  -- the frame record at 0x6bb2
  have hprivx : E.S.priv x.m.memory = E.S.priv s.m.memory := E.S.priv_local _ _ hM.low
  have hFx : ∀ f st', E.S.file s.m.memory f st' → E.S.file y.m.memory f st' := by
    intro f st' h
    have h1 : E.S.file x.m.memory f st' := (E.S.local_ _ _ _ _ (fun a ha => hM.low a (E.S.foot_lo _ _ _ _ h ha)) h).1
    rw [hmy]
    refine (E.S.local_ _ _ _ _ (storeMem_keeps fun a ha => ?_) h1).1
    have hp := E.S.foot_priv _ _ _ _ h1 ha
    rw [hprivx] at hp
    by_contra hc
    have : a = (b + 0xa160#64).toNat := by omega
    exact hHRp (this ▸ hp)
  have hreg : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, r ≠ .rbx → y.m.core.read r = x.m.core.read r := hcsy
  have hsl : ∀ o, o ≤ 216 → 8 ≤ o → y.m.memory.readBytes ((s.m.core.read .rsp).toNat - o) 8 =
      x.m.memory.readBytes ((s.m.core.read .rsp).toNat - o) 8 := fun o h1 h2 => by
    rw [hmy, storeMem_read_ne (by rcases hHRout with h | h <;> omega)]
  have hFb : ∀ f st', E.S.file (hrBase b s).m.memory f st' → E.S.file s.m.memory f st' := by
    intro f st' h
    have hpk : E.S.priv (hrBase b s).m.memory = E.S.priv s.m.memory :=
      E.S.priv_keep _ _ (storeMem_keeps fun a ha => by
        by_contra hc
        have : a = (b + 0xa160#64).toNat := by omega
        exact hHRp (this ▸ ha))
    refine (E.S.local_ _ _ _ _ (fun a ha => ?_) h).1
    have hp := E.S.foot_priv _ _ _ _ h ha
    rw [hpk] at hp
    have hne : a ≠ (b + 0xa160#64).toNat := fun he => hHRp (he ▸ hp)
    refine ⟨?_, fun acc => rfl⟩
    simp only [hrBase, storeMem]
    rw [Memory.install_outside _ _ _ _ (by simp [Silmaril.X86.Ext.leBytes]; omega)]
  have hLy : LibK E W (hrBase b s).m.memory y.m.memory := by
    have hk : Keeps (fun a => a < E.S.lo ∧ a ≠ (b + 0xa160#64).toNat) (hrBase b s).m.memory y.m.memory := by
      intro a ha
      have h1 := storeMem_keeps (P := fun c => c ≠ (b + 0xa160#64).toNat) (m := x.m.memory) (a := b + 0xa160#64)
        (k := 1) (v := BitVec.setWidth 64 1#8) (fun c hc => by omega) a ha.2
      have h2 := storeMem_keeps (P := fun c => c ≠ (b + 0xa160#64).toNat) (m := s.m.memory) (a := b + 0xa160#64)
        (k := 1) (v := BitVec.setWidth 64 1#8) (fun c hc => by omega) a ha.2
      rw [hmy]; dsimp only [hrBase]
      exact ⟨by rw [h1.1, h2.1, (hM.low a ha.1).1], fun acc => by rw [h1.2, h2.2, (hM.low a ha.1).2]⟩
    have hpk : E.S.priv (hrBase b s).m.memory = E.S.priv s.m.memory :=
      E.S.priv_keep _ _ (storeMem_keeps fun a ha => by
        by_contra hc
        have : a = (b + 0xa160#64).toNat := by omega
        exact hHRp (this ▸ ha))
    have hp : E.S.priv y.m.memory = E.S.priv (hrBase b s).m.memory :=
      E.S.priv_keep _ _ (hk.mono fun a ha => ⟨E.S.priv_lo _ _ ha, fun he => by
        rw [hpk] at ha; exact hHRp (he ▸ ha)⟩)
    exact ⟨hk.mono fun a ha => ⟨ha.1, fun he => ha.2.1 (he ▸ hHRk)⟩, fun a ha => by rw [hp]; exact ha.2.2.1⟩
  refine k _ ⟨fun a h => Or.inr (hX a (Or.inl h)).2, hlo, hal, hBy.of_eq rfl (by simp) rfl rfl, ?_, by simp [hbxy],
    ?_, ?_, ?_, ?_, hrdx, hFx _ _ hfile, by simp [hrBase, hgy, hM.g], fun f st' _ h => hFx f st' (hFb f st' h),
    ⟨fun a h => (hX a h).2, fun a h acc => by
      rw [hmy]; unfold Memory.permits; simp only [storeMem, hrBase]; rw [hM.regs]⟩, hLy⟩ (by simp)
    (by simp [hbxy])
  · simp only [st_read_mk, Silmaril.Machine.RegisterFile.write_other, ne_eq, reduceCtorEq,
      not_false_eq_true, st_regs_apply]
    rw [hreg .rbp (by simp [Silmaril.X86.sysv64_calleeSaved]) (by decide)]; exact hM.rbp
  · simp only [st_read_mk, Silmaril.Machine.RegisterFile.write_other, ne_eq, reduceCtorEq,
      not_false_eq_true, st_regs_apply]
    rw [hreg .r14 (by simp [Silmaril.X86.sysv64_calleeSaved]) (by decide)]; exact h14x
  · dsimp only [hrBase]; rw [hsl 200 (by decide) (by decide)]; exact hM.slot2
  · dsimp only [hrBase]; rw [hsl 64 (by decide) (by decide)]; exact hM.slot3
  · dsimp only [hrBase]; show y.m.memory.readBytes _ 1 = _
    rw [hmy, storeMem_read_ne (by omega)]; exact hM.miss

/-- The imports of `digest_file ("-")`: those of a named file and `clearerr_unlocked`. -/
structure StdinImps (E : Env) (R : ShaRep) (W : World) (b lb kb : Word) : Prop where
  dig : DigImps E R W b lb kb
  clearerr : ImpOk W (lb + 0x91400#64) (nm "clearerr_unlocked") (clearerrStep E W)

theorem _root_.Silmaril.Elf.Link.Dyn.Proc.BodyX.withM {W : World} {M M' : Memory → Prop} {s u : PState}
    {fr n : Nat} {saved : List (Nat × Word)} {X : Nat → Prop} (h : BodyX W M s u fr n saved X)
    (hm : M' u.m.memory) : BodyX W M' s u fr n saved X :=
  ⟨h.rsp, h.keepX, h.room, hm, h.fs, h.done, h.saved, h.perm⟩

/-- The image facts and `clearerr_unlocked`'s GOT slot. -/
def ShaMemCL (b lb kb : Word) (m : Memory) : Prop :=
  ShaMemCD b lb kb m ∧ loadN m (b + 0x9f68#64) 8 = some (lb + 0x91400#64)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- **`digest_file ("-")`'s end** (`0x6b50`): `clearerr_unlocked (stdin)`, return 1. -/
theorem dg_tail_stdin {E : Env} {R : ShaRep} {W : World} {b lb kb : Word} (I : StdinImps E R W b lb kb)
    {X : Nat → Prop} {Q : PState → Prop} {s x : PState} {F g : Word} {data : List Byte} {st : St}
    (hF : DigFin E W b lb kb X s x F g 0#32 data st) (hrip : x.m.core.rip = b + 0x6b50#64)
    (habi : AbiEntry s.m.core s.m.memory)
    (hguard : loadN s.m.memory (s.m.core.fsBase + 0x28#64) 8 = some g)
    (hgk : ∀ j, j < 8 → W.Kept ((s.m.core.fsBase + 0x28#64).toNat + j))
    (hX : ∀ x, X x → x + 1024 < (s.m.core.read .rsp).toNat ∨ (s.m.core.read .rsp).toNat + 8 ≤ x)
    (hgX : ∀ j, j < 8 → ¬ X ((s.m.core.fsBase + 0x28#64).toNat + j))
    (hclr : loadN x.m.memory (b + 0x9f68#64) 8 = some (lb + 0x91400#64))
    (hbinhi : (s.m.core.read .rsp).toNat + 8 ≤ (s.m.core.read .rsi).toNat)
    (hrdxhi : (s.m.core.read .rsp).toNat + 8 ≤ (s.m.core.read .rdx).toNat)
    (k : ∀ t, AbiReturn s.m.core s.m.memory t.m.core →
      Keeps (fun a => (W.Kept a ∨ (s.m.core.read .rsp).toNat ≤ a) ∧ ¬ X a) s.m.memory t.m.memory →
      t.m.memory.readBytes (s.m.core.read .rsi).toNat 32 = some (sha256 data) →
      t.m.memory.readBytes (s.m.core.read .rdx).toNat 1 = some [0#8] →
      low32 (t.m.core.read .rax) = 1#32 → t.g = s.g →
      E.S.file t.m.memory F { st with eof := false, err := false } →
      (∀ f st', f ≠ F → E.S.file s.m.memory f st' → E.S.file t.m.memory f st') →
      t.m.core.fsBase = s.m.core.fsBase → PermKept s t.m.memory → PermDX s t.m.memory → MustQ W Q t) :
    MustQ W Q x := by
  have hin : ∀ n, n < 0xa188 → W.InImage (b + BitVec.ofNat 64 n).toNat := fun n hn =>
    sha_in' I.dig.cl.img I.dig.cl.hb hn
  have hB := hF.body
  have hlo := hF.lo
  have hsv := sv6_bound s
  have hal216 : ((s.m.core.read .rsp).toNat - 216) % 16 = 0 := by have := hF.al; omega
  have hMk : ∀ m m', ShaMemCL b lb kb m → Keeps W.InImage m m' → ShaMemCL b lb kb m' := by
    intro m m' hm hk
    refine ⟨shaMemCD_keep I.dig.cl.img I.dig.cl.hb _ _ hm.1 hk, ?_⟩
    rw [hk.loadN fun j hj => by
      rw [show (b + 0x9f68#64).toNat + j = (b + BitVec.ofNat 64 (0x9f68 + j)).toNat by
        rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (show 0x9f68 < 2 ^ 64 by decide), Nat.mod_eq_of_lt (show 0x9f68 + j < 2 ^ 64 by omega),
          Nat.mod_eq_of_lt (by have := I.dig.cl.hb; omega), Nat.mod_eq_of_lt (by have := I.dig.cl.hb; omega)]; omega]
      exact hin _ (by omega)]
    exact hm.2
  have hz : Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.logicFlagsN
      (andD (BitVec.setWidth 32 (x.m.core.read .r14)) (BitVec.setWidth 32 (x.m.core.read .r14)))) .ne = some false := by
    rw [eval_ne_testD, hF.r14]; simp
  refine must_listed (o := 272) shaD_listing_ok.2.2 rfl hB.done (by rw [hrip]; exact hin _ (by decide))
    hB.mem.2.digestFile (by rw [hrip, ripadd]) ?_
  xstep [hrip]
  refine must_listed (o := 275) shaD_listing_ok.2.2 rfl hB.done (hin _ (by decide)) hB.mem.2.digestFile (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 278) shaD_listing_ok.2.2 rfl hB.done (hin _ (by decide)) hB.mem.2.digestFile (by rw [ripadd]) ?_
  xstep [hz]
  refine must_gen (fun y => BodyX W (ShaMemCL b lb kb) s y 216 1024 (sv6 s) X ∧ y.m.core.rip = b + 0x6b5c#64 ∧
      y.m.memory = x.m.memory ∧ y.g = x.g ∧ y.m.core.read .rdi = F ∧
      (∀ r ∈ Silmaril.X86.sysv64.calleeSaved, y.m.core.read r = x.m.core.read r)) ?_ ?_
  · refine ⟨(hB.withM ⟨hB.mem, hclr⟩).of_eq rfl (by simp) rfl rfl, by simp, rfl, rfl, by simp [hF.rbx], ?_⟩
    intro r hr
    simp only [Silmaril.X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  rintro y ⟨hBy, hry, hmy, hgy, hdiy, hcsy⟩
  have hyr : (y.m.core.read .rsp).toNat = (s.m.core.read .rsp).toNat - 216 := by
    rw [hBy.rsp]; exact sub_toNat (by omega) (by decide)
  have hy8 : (y.m.core.read .rsp - 8#64).toNat = (s.m.core.read .rsp).toNat - 224 := by
    rw [sub_toNat (k := 8) (by rw [hyr]; omega) (by decide), hyr]; omega
  have hlo8 : E.S.lo ≤ (y.m.core.read .rsp - 8#64).toNat := by rw [hy8]; omega
  have hfy : E.S.file (pushMem y.m.memory (y.m.core.read .rsp) (b + 27200#64 + BitVec.ofNat 64 (284 + 5))) F st :=
    file_push (by rw [hmy]; exact hF.file) hlo8
  refine body_callK hMk hBy (by decide) (by decide) hsv hal216 I.dig.cl.lz
    (o := 284) (so := 0x320) (pb := b + 0x23c0#64) (fp := fun _ => False)
    shaD_listing_ok.2.2 rfl (by rw [hry]; exact hin _ (by decide)) (fun m h => h.1.2.digestFile)
    (by rw [hry, ripadd]) shaC_listing_ok.1 rfl rfl (by simp only [BitVec.add_assoc]; rfl)
    (img_off I.dig.cl.img I.dig.cl.hb (by decide)) (img_off I.dig.cl.img I.dig.cl.hb (by decide))
    (fun m h => h.1.1.plt)
    (fun m h => by
      rw [show b + 0x23c0#64 + BitVec.ofNat 64 (0x320 + 4 + 6) + BitVec.signExtend 64 0x787e#32 = b + 0x9f68#64 by
        simp only [BitVec.add_assoc]; rfl]
      exact h.2)
    I.clearerr.1 I.clearerr.2.1 I.clearerr.2.2.1 (fun r h => (impOk_fn I.clearerr _ r).1 h)
    (fun he => ⟨he, ⟨st, by rw [callEntry_mem, callEntry_read _ _ _ (by decide), hdiy]; exact hfy⟩,
      by rw [callEntry_rsp]; exact hlo8⟩)
    (fun v hv => ⟨hv.1.1, hv.1.2.2.1, by simpa [callEntry] using hv.1.2.1, by rw [hv.2.1]; exact hBy.done⟩)
    (fun x h => h.elim) hX ?_
  intro v hv hBv hrv hspv hcsv hkv
  obtain ⟨-, hgv, hoth, hclrv⟩ := hv
  unfold OthersKept at hoth
  simp only [callEntry_mem, callEntry_read _ _ _ (by decide : Reg.rdi ≠ .rsp), hdiy] at hoth hclrv
  have hkx : Keeps (fun a => (W.Kept a ∨ (s.m.core.read .rsp).toNat - 216 ≤ a)) x.m.memory v.m.memory := by
    rw [← hmy]; exact hkv.mono fun a ha => ⟨ha, id⟩
  refine dg_epi I.dig.cl (hBv.withM hBv.mem.1) (by rw [hrv]; simp only [BitVec.add_assoc]; rfl) ?_ ?_ habi hguard hgk
    hX hgX ?_
  · rw [hcsv .rbp (by simp [Silmaril.X86.sysv64_calleeSaved]), hcsy .rbp (by simp [Silmaril.X86.sysv64_calleeSaved])]
    exact hF.rbp
  · rw [hkx.readBytes (fun j hj => Or.inr (by omega))]; exact hF.sg
  intro t habi2 hm2 hax2 hg2 hfs2
  refine k t habi2 (by rw [hm2]; exact hBv.keepX) ?_ ?_ hax2 ?_ ?_ ?_ hfs2 (by rw [hm2]; exact hBv.perm)
    (by rw [hm2]; exact hF.pdx.keep hkx fun a _ ha => Or.inr (by omega))
  · rw [hm2, hkx.readBytes (fun j hj => Or.inr (by omega))]; exact hF.bin
  · rw [hm2, hkx.readBytes (fun j hj => Or.inr (by omega))]; exact hF.miss
  · rw [hg2, hgv]; simp only [callEntry_g]; rw [hgy]; exact hF.g
  · rw [hm2]; exact hclrv st hfy
  · intro f st' hne h
    rw [hm2]; exact hoth f st' (by simpa using hne) (file_push (by rw [hmy]; exact hF.others f st' hne h) hlo8)

/-- What `digest_file ("-")`'s caller provides. -/
structure DigEntryStdin (E : Env) (W : World) (b lb kb : Word) (s : PState) (g Fi : Word) (st : St) : Prop where
  rip : s.m.core.rip = b + 0x6a40#64
  abi : AbiEntry s.m.core s.m.memory
  room : Room W s.m.memory (s.m.core.read .rsp) 1024
  lo : E.S.lo + 1024 ≤ (s.m.core.read .rsp).toNat
  done : s.g.done = none
  mem : ShaMemCD b lb kb s.m.memory
  /-- the name `"-"`, in the program's kept memory -/
  name : s.m.memory.readBytes (s.m.core.read .rdi).toNat 2 = some [0x2d#8, 0#8]
  namek : ∀ j, j < 2 → W.Kept ((s.m.core.read .rdi).toNat + j)
  nameb : (s.m.core.read .rdi).toNat + 1 < 2 ^ 64
  outs : ∀ a, DX s a → ¬ W.Kept a ∧ (s.m.core.read .rsp).toNat + 8 ≤ a
  binw : s.m.memory.Permitted .write (s.m.core.read .rsi).toNat 32
  binr : s.m.memory.Permitted .read (s.m.core.read .rsi).toNat 32
  missw : s.m.memory.Permitted .write (s.m.core.read .rdx).toNat 1
  missr : s.m.memory.Permitted .read (s.m.core.read .rdx).toNat 1
  disj : (s.m.core.read .rsi).toNat + 32 ≤ (s.m.core.read .rdx).toNat ∨
    (s.m.core.read .rdx).toNat + 1 ≤ (s.m.core.read .rsi).toNat
  guard : loadN s.m.memory (s.m.core.fsBase + 0x28#64) 8 = some g
  guardk : ∀ j, j < 8 → W.Kept ((s.m.core.fsBase + 0x28#64).toNat + j)
  guardHR : ∀ j, j < 8 → (s.m.core.fsBase + 0x28#64).toNat + j ≠ (b + 0xa160#64).toNat
  /-- libc's `stdin` variable, through the GOT -/
  got : loadN s.m.memory (b + 0x9fb8#64) 8 = some (lb + 0x2056b0#64)
  var : loadN s.m.memory (lb + 0x2056b0#64) 8 = some Fi
  vark : ∀ j, j < 8 → W.Kept ((lb + 0x2056b0#64).toNat + j)
  varHR : ∀ j, j < 8 → (lb + 0x2056b0#64).toNat + j ≠ (b + 0xa160#64).toNat
  fi : Fi ≠ 0#64
  /-- `have_read_stdin`: writable, the program's -/
  hrw : s.m.memory.Permitted .write (b + 0xa160#64).toNat 1
  hrp : ¬ E.S.priv s.m.memory (b + 0xa160#64).toNat
  hrr : s.m.memory.Permitted .read (b + 0xa160#64).toNat 1
  /-- `clearerr_unlocked`'s GOT slot -/
  clr : loadN s.m.memory (b + 0x9f68#64) 8 = some (lb + 0x91400#64)
  /-- standard input: open for reading, no error -/
  file : E.S.file s.m.memory Fi st
  stok : st.fail = false ∧ st.err = false ∧ st.reading = true ∧ st.fd < 2 ^ 31 ∧ (st.eof = true → st.rd = [])
  /-- the library's resources for one `malloc (BLOCKSIZE + 72)` -/
  res : InMain s.g ∧ s.g.allocs < E.maxAllocs ∧ s.g.heap + 0x8048 ≤ E.maxHeap

/-- What `digest_file ("-")` guarantees on return: the digest of what was left on standard input,
which is now at its end with the indicators cleared. -/
structure DigExitStdin (E : Env) (W : World) (b : Word) (s t : PState) (Fi : Word) (st : St) : Prop where
  abi : AbiReturn s.m.core s.m.memory t.m.core
  keep : Keeps (fun a => (W.Kept a ∨ (s.m.core.read .rsp).toNat ≤ a) ∧ ¬ (DX s a ∨ HR b a)) s.m.memory t.m.memory
  digest : t.m.memory.readBytes (s.m.core.read .rsi).toNat 32 = some (sha256 st.rd)
  missing : t.m.memory.readBytes (s.m.core.read .rdx).toNat 1 = some [0#8]
  ok : low32 (t.m.core.read .rax) = 1#32
  /-- the library state after the buffer's `malloc` -/
  g : t.g = s.g.alloc 0x8048
  stdin : ∃ st', E.S.file t.m.memory Fi st' ∧ st'.rd = [] ∧ st'.eof = false ∧ st'.err = false ∧
    st'.fail = false ∧ st'.reading = true ∧ st'.fd = st.fd
  streams : ∀ f st', f ≠ Fi → E.S.file s.m.memory f st' → E.S.file t.m.memory f st'
  fs : t.m.core.fsBase = s.m.core.fsBase
  perm : PermKept s t.m.memory
  /-- the permissions of `bin_result` and `missing` are as at entry -/
  permDX : PermDX s t.m.memory
  /-- `have_read_stdin = true` -/
  hr : t.m.memory.readBytes (b + 0xa160#64).toNat 1 = some [1#8]

/-- **`digest_file ("-")` on standard input.** -/
def Task.digestStdin (E : Env) (R : ShaRep) (W : World) (b lb kb : Word) : Prop :=
  StdinImps E R W b lb kb → ∀ (Q : PState → Prop) (s : PState) (g Fi : Word) (st : St),
    DigEntryStdin E W b lb kb s g Fi st → (∀ t, DigExitStdin E W b s t Fi st → MustQ W Q t) → MustQ W Q s

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem task_digestStdin {E : Env} {R : ShaRep} {W : World} {b lb kb : Word} : Task.digestStdin E R W b lb kb := by
  intro I Q s g Fi st hE k
  have hroom := hE.room
  have hKout : ∀ a, W.Kept a → a < (s.m.core.read .rsp).toNat - 1024 ∨ (s.m.core.read .rsp).toNat + 8 ≤ a := by
    intro a ha
    by_contra hc
    exact (hroom.2.2 a (by omega) (by omega)).2.2 ha
  have hHRk : W.Kept (b + 0xa160#64).toNat := Or.inl (sha_in' I.dig.cl.img I.dig.cl.hb (n := 0xa160) (by decide))
  have hc0 : s.m.memory.readBytes (s.m.core.read .rdi).toNat 1 = some [0x2d#8] := by
    have h := Memory.readBytes_sub_range hE.name (offset := 0) (len := 1) (by omega) (by omega)
    simpa using h
  have hc1 : s.m.memory.readBytes ((s.m.core.read .rdi).toNat + 1) 1 = some [0#8] := by
    have h := Memory.readBytes_sub_range hE.name (offset := 1) (len := 1) (by omega) (by omega)
    simpa using h
  refine sha_digest_pro I.dig.cl hE.rip hE.room hE.done hE.mem (fun u hP => ?_)
  refine sha_digest_mid_dash I.dig hP hE.lo hE.namek hc0 rfl hc1 hE.nameb hE.outs hE.missw hE.missr hE.guard
    hE.guardk (fun x hM hrx h14 => ?_)
  refine sha_digest_stdin_head I.dig hM hrx h14 hE.lo hE.abi.aligned hE.outs hE.got hE.var hE.vark hE.varHR hE.fi
    hE.hrw hE.hrp hE.file (fun u hF hru hdi => ?_)
  refine dg_setup I.dig hF hru hdi hE.stok hE.res (fun v buf hP hrv => ?_)
  refine dg_init I.dig hP hrv (fun v hv hrv => ?_)
  refine dg_loop I.dig hv hrv (by simp) (fun v a p' st' hv' hrv' hrd herr hfd => ?_)
  refine dg_flush I.dig hv' hrv' hrd (fun v2 hd hr2 => ?_)
  have hHRn : (b + 0xa160#64).toNat = b.toNat + 0xa160 := by
    have := I.dig.cl.hb
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hHRout := hKout _ hHRk
  have hst : ∀ {P : Nat → Prop}, (∀ a, P a → a ≠ (b + 0xa160#64).toNat) →
      Keeps P s.m.memory (hrBase b s).m.memory := fun hP =>
    storeMem_keeps fun a ha => by have := hP a ha; omega
  have hbX : ∀ a, BR (hrBase b s) a → ¬ MX s a ∧ ¬ W.Kept a ∧ ((hrBase b s).m.core.read .rsp).toNat + 8 ≤ a ∧
      ¬ (((hrBase b s).m.core.read .rdx).toNat ≤ a ∧ a < ((hrBase b s).m.core.read .rdx).toNat + 1) := by
    intro a ha
    have h := hE.outs a (Or.inr ha)
    have hd := hE.disj
    unfold BR hrBase at ha
    simp only at ha ⊢
    simp only [hrBase]
    exact ⟨fun hm => by unfold MX at hm; omega, h.1, h.2, fun hm => by omega⟩
  refine dg_final I.dig hd hr2 hbX (by simp only [hrBase]; rw [storeMem_permitted]; exact hE.binw)
    (by simp only [hrBase]; rw [storeMem_permitted]; exact hE.binr) (fun v3 hf hr3 => ?_)
  have hXp : ∀ a, (MX s a ∨ BR (hrBase b s) a) → a + 1024 < ((hrBase b s).m.core.read .rsp).toNat ∨
      ((hrBase b s).m.core.read .rsp).toNat + 8 ≤ a := by
    rintro a (h | h)
    · exact Or.inr (hE.outs a (Or.inl h)).2
    · exact Or.inr (hE.outs a (Or.inr h)).2
  have hnX : ∀ a, W.Kept a → ¬ (MX s a ∨ BR (hrBase b s) a) := by
    rintro a ha (h | h)
    · exact (hE.outs a (Or.inl h)).1 ha
    · exact (hE.outs a (Or.inr h)).1 ha
  have hbn : ∀ j, j < 8 → (b + 0x9f68#64).toNat + j = (b + BitVec.ofNat 64 (0x9f68 + j)).toNat := fun j hj => by
    have := I.dig.cl.hb
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show 0x9f68 < 2 ^ 64 by decide), Nat.mod_eq_of_lt (show 0x9f68 + j < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  have hclr : loadN v3.m.memory (b + 0x9f68#64) 8 = some (lb + 0x91400#64) := by
    have hk : ∀ j, j < 8 → W.Kept ((b + 0x9f68#64).toNat + j) := fun j hj =>
      Or.inl (by rw [hbn j hj]; exact sha_in' I.dig.cl.img I.dig.cl.hb (by omega))
    rw [hf.body.keepX.loadN fun j hj => ⟨Or.inl (hk j hj), hnX _ (hk j hj)⟩,
      (hst (P := fun a => ∃ j, j < 8 ∧ a = (b + 0x9f68#64).toNat + j) fun a ⟨j, hj, he⟩ => by
        have := I.dig.cl.hb
        rw [he, hHRn, show (b + 0x9f68#64).toNat = b.toNat + 0x9f68 by
          rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]]; omega).loadN
      fun j hj => ⟨j, hj, rfl⟩]
    exact hE.clr
  have hret : (hrBase b s).m.memory.readBytes (s.m.core.read .rsp).toNat 8 =
      s.m.memory.readBytes (s.m.core.read .rsp).toNat 8 := by
    simp only [hrBase]; rw [storeMem_read_ne (by omega)]
  have habi' : AbiEntry (hrBase b s).m.core (hrBase b s).m.memory :=
    ⟨hE.abi.aligned, by
      show (hrBase b s).m.memory.readBytes (s.m.core.read .rsp).toNat 8 = _
      rw [hret, hE.abi.returnAddress]
      unfold Silmaril.X86.FnContract.retOf
      rw [show (hrBase b s).m.core = s.m.core from rfl, hret]⟩
  have hguard' : loadN (hrBase b s).m.memory ((hrBase b s).m.core.fsBase + 0x28#64) 8 = some g := by
    rw [show (hrBase b s).m.core.fsBase = s.m.core.fsBase from rfl, (hst (P := fun a => ∃ j, j < 8 ∧ a = (s.m.core.fsBase + 0x28#64).toNat + j) fun a ⟨j, hj, he⟩ => by
      rw [he]; exact hE.guardHR j hj).loadN fun j hj => ⟨j, hj, rfl⟩]
    exact hE.guard
  refine dg_tail_stdin (s := { hrBase b s with g := (hrBase b s).g.alloc 0x8048 }) I hf hr3 habi' hguard'
    hE.guardk hXp (fun j hj => hnX _ (hE.guardk j hj)) hclr
    (hE.outs _ (Or.inr ⟨le_refl _, by omega⟩)).2 (hE.outs _ (Or.inl ⟨le_refl _, by omega⟩)).2 ?_
  intro t habi hkeep hdig hmiss hax hg hstd hoth hfs hperm hpdx
  have hfwd : ∀ f st', E.S.file s.m.memory f st' → E.S.file (hrBase b s).m.memory f st' := by
    intro f st' h
    refine (E.S.local_ _ _ _ _ (hst fun a ha he => hE.hrp (he ▸ E.S.foot_priv _ _ _ _ h ha)) h).1
  have hpc : t.m.core.rip = Silmaril.X86.FnContract.retOf s.m.core s.m.memory := by
    rw [habi.pc]; unfold Silmaril.X86.FnContract.retOf
    rw [show (hrBase b s).m.core = s.m.core from rfl, hret]
  refine k t ⟨⟨hpc, habi.stack, habi.calleeSaved⟩,
    (hst fun a ha he => ha.2 (Or.inr he)).trans (hkeep.mono fun a ha => ⟨ha.1, fun h => ha.2 (by
      rcases h with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h))⟩), hdig, hmiss, hax, hg,
    ⟨_, hstd, by simp [hf.stok.2.2.2.2], rfl, rfl, by simp [hf.stok.1], by simp [hf.stok.2.2.1], by simp [hfd]⟩,
    fun f st' hne h => hoth f st' hne (hfwd f st' h), hfs, hperm,
    ⟨hpdx.pos, fun a ha acc => by rw [hpdx.perm a ha acc]; rfl⟩, ?_⟩
  have hHRx : ¬ (MX s (b + 0xa160#64).toNat ∨
      BR { hrBase b s with g := (hrBase b s).g.alloc 0x8048 } (b + 0xa160#64).toNat) := hnX _ hHRk
  rw [hkeep.readBytes (fun j hj => by
    have : j = 0 := by omega
    subst this; exact ⟨Or.inl (by simpa using hHRk), by simpa using hHRx⟩)]
  simp only [hrBase]
  rw [storeMem_read hE.hrr]
  rfl

end Silmaril.Elf.Link.Dyn.Sha256sum
