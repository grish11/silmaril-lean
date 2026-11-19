module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.Close

/-! # GNU `sha256sum`: `rpl_fclose` on an input stream

`rplTail`: from `rpl_fclose`'s epilogue (`0x4334`) through the tail call of `fclose`, for any
stream; `sha_rplFclose_in`: the whole of `rpl_fclose` on a stream open for reading (gnulib
asks `__freading`, `lseek`s, and flushes before closing), with no error.
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
open Silmaril.Elf.Link.Dyn.Hello (abiEntry_of retOf_of)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- **The tail of `rpl_fclose`** (`0x4334`): restore the saved registers and tail-call `fclose`. -/
theorem rplTail {E : Env} {W : World} {b lb : Word} (I : CloseImps E W b lb) {Q : PState → Prop}
    {s w : PState} (habi : AbiEntry s.m.core s.m.memory)
    (hB : Body W (ShaMemC b lb) s w 40 256 (sv4 s)) (hrip : w.m.core.rip = b + 17204#64)
    (hrbx : w.m.core.read .rbx = s.m.core.read .rdi) (h14 : w.m.core.read .r14 = s.m.core.read .r14)
    (h15 : w.m.core.read .r15 = s.m.core.read .r15)
    {st : St} (hf : E.S.file w.m.memory (s.m.core.read .rdi) st) (he : st.err = false)
    (hrel : st.fd = 1 → W.reliable = true) {m0 : Memory} (hL : LibK E W m0 w.m.memory)
    (k : ∀ t, AbiReturn s.m.core s.m.memory t.m.core →
      Keeps (fun a => W.Kept a ∨ (s.m.core.read .rsp).toNat ≤ a) s.m.memory t.m.memory →
      t.g.out = w.g.out ++ (if st.fd = 1 then st.buf else []) → t.g.jobs = w.g.jobs →
      t.g.atexit = w.g.atexit → t.g.done = none → t.g.inp = w.g.inp → t.g.err = w.g.err →
      (t.g.allocs = w.g.allocs ∧ t.g.heap = w.g.heap ∧ t.g.files = w.g.files) →
      low32 (t.m.core.read .rax) = 0#32 →
      (∀ f' st', f' ≠ s.m.core.read .rdi → E.S.file w.m.memory f' st' → E.S.file t.m.memory f' st') →
      t.m.core.fsBase = s.m.core.fsBase → PermKept s t.m.memory → LibK E W m0 t.m.memory → MustQ W Q t) :
    MustQ W Q w := by
  have hin : ∀ n, n < 0xa188 → W.InImage (b + BitVec.ofNat 64 n).toNat := fun n hn => sha_in' I.img I.hb hn
  have hsp := hB.room.1
  have hd := hB.done
  have hwr : (w.m.core.read .rsp).toNat = (s.m.core.read .rsp).toNat - 40 := by
    rw [hB.rsp]; exact sub_toNat (by omega) (by decide)
  have q8 : ((w.m.core.read .rsp).toNat + 8) % 18446744073709551616 = (s.m.core.read .rsp).toNat - 32 := by
    rw [hwr]; omega
  have q16 : ((w.m.core.read .rsp).toNat + 16) % 18446744073709551616 = (s.m.core.read .rsp).toNat - 24 := by
    rw [hwr]; omega
  have q24 : ((w.m.core.read .rsp).toNat + 24) % 18446744073709551616 = (s.m.core.read .rsp).toNat - 16 := by
    rw [hwr]; omega
  have q32 : ((w.m.core.read .rsp).toNat + 32) % 18446744073709551616 = (s.m.core.read .rsp).toNat - 8 := by
    rw [hwr]; omega
  have sv1 := hB.saved (32, s.m.core.read .rbx) (by simp [sv4])
  have sv2 := hB.saved (24, s.m.core.read .r12) (by simp [sv4])
  have sv3 := hB.saved (16, s.m.core.read .r13) (by simp [sv4])
  have sv5 := hB.saved (8, s.m.core.read .rbp) (by simp [sv4])
  simp only at sv1 sv2 sv3 sv5
  have hsp40 : w.m.core.read .rsp + 40#64 = s.m.core.read .rsp := by
    rw [hB.rsp]; exact BitVec.sub_add_cancel _ _
  have hretk : w.m.memory.readBytes (s.m.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [Silmaril.X86.FnContract.retOf s.m.core s.m.memory]) := by
    rw [(Body.keep hB).readBytes (fun j hj => Or.inr (by omega))]; exact habi.returnAddress
  refine must_listed (o := 132) shaC_listing_ok.2.1 rfl hd (by rw [hrip]; exact hin _ (by decide))
    hB.mem.rplFclose (by rw [hrip, ripadd]) ?_
  xstep [hrip]
  refine must_listed (o := 135) shaC_listing_ok.2.1 rfl hd (hin _ (by decide)) hB.mem.rplFclose (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 139) shaC_listing_ok.2.1 rfl hd (hin _ (by decide)) hB.mem.rplFclose (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, q8, sv1]
  refine must_listed (o := 140) shaC_listing_ok.2.1 rfl hd (hin _ (by decide)) hB.mem.rplFclose (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, q16, sv2]
  refine must_listed (o := 142) shaC_listing_ok.2.1 rfl hd (hin _ (by decide)) hB.mem.rplFclose (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, q24, sv3]
  refine must_listed (o := 144) shaC_listing_ok.2.1 rfl hd (hin _ (by decide)) hB.mem.rplFclose (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, q32, sv5]
  refine must_plt_jmp (o := 145) (so := 0x160) (pb := b + 0x23c0#64) hd I.lz shaC_listing_ok.2.1 rfl
    (hin _ (by decide)) hB.mem.rplFclose (by rw [ripadd]) shaC_listing_ok.1 rfl rfl
    (by simp only [BitVec.add_assoc]; rfl)
    (img_off I.img I.hb (by decide)) (img_off I.img I.hb (by decide)) hB.mem.plt
    (by
      rw [show b + 0x23c0#64 + BitVec.ofNat 64 (0x160 + 4 + 6) + BitVec.signExtend 64 0x795e#32 = b + 0x9e88#64 by
        simp only [BitVec.add_assoc]; rfl]
      exact hB.mem.fclose)
    I.fclose.1 I.fclose.2.1 I.fclose.2.2.1 (fun r h => (impOk_fn I.fclose _ r).1 h)
    ⟨abiEntry_of (v := Silmaril.X86.FnContract.retOf s.m.core s.m.memory)
        (by simp [jmpEntry, hsp40]; exact habi.aligned) (by simpa [jmpEntry, hsp40] using hretk),
      _, by simpa [jmpEntry, hrbx] using hf⟩ ?_
  rintro t ⟨hLR, hjT, haT, hdT, hiT, heT, hcaT, hchT, hcfT, hokT, hclT⟩
  have hLt : LibK E W m0 t.m.memory := LibK.libRet (by exact hL) hLR fun _ _ h => h
  obtain ⟨⟨habiT, hkT⟩, hfsT, hspT, -, -⟩ := hLR
  have hcl := hclT _ (by simpa [jmpEntry, hrbx] using hf)
  have hgT : t.g.out = w.g.out ++ (if st.fd = 1 then st.buf else []) ∧ low32 (t.m.core.read .rax) = 0#32 := by
    simp only [jmpEntry] at hcl ⊢
    by_cases h1 : st.fd = 1
    · rcases hcl.1 h1 with ⟨ho, hz⟩ | ⟨hu, -⟩
      · exact ⟨by rw [ho]; simp [h1], hz he⟩
      · rw [hrel h1] at hu; cases hu
    · obtain ⟨ho, hz⟩ := hcl.2 h1
      exact ⟨by rw [ho]; simp [h1], hz he⟩
  refine k t ⟨?_, ?_, ?_⟩ ?_ hgT.1 (by rw [hjT]; rfl) (by rw [haT]; rfl) hdT (by rw [hiT]; rfl) (by rw [heT]; rfl)
    ⟨by rw [hcaT]; rfl, by rw [hchT]; rfl, by rw [hcfT]; rfl⟩ hgT.2 ?_
    (by rw [hfsT]; exact hB.fs) ?_ hLt
  · rw [habiT.pc]; exact retOf_of (by simpa [jmpEntry, hsp40] using hretk)
  · rw [habiT.stack]; simp [jmpEntry, hsp40]
  · intro r hr
    rw [habiT.calleeSaved r hr]
    simp only [Silmaril.X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [jmpEntry, h14, h15]
  · refine (Body.keep hB).trans (hkT.mono fun x hx => ⟨?_, fun h => h⟩)
    rcases hx with h | h
    · exact Or.inl h
    · right; simp [jmpEntry, hsp40]; omega
  · intro f' st' hne h
    exact hokT f' st' (by simpa [jmpEntry, hrbx] using hne) (by simpa [jmpEntry] using h)
  · intro x h1 h2 acc
    unfold StackPerm at hspT
    simp only [jmpEntry, st_read_mk, Silmaril.Machine.RegisterFile.write_same,
      Silmaril.Machine.RegisterFile.write_other, ne_eq, reduceCtorEq, not_false_eq_true, hsp40] at hspT
    rw [hspT x (range_mb h1 h2).1 (range_mb h1 h2).2 acc]
    exact hB.perm x h1 h2 acc

theorem eval_ne_cmp (x y : BitVec 64) :
    Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.AluOp.flagsN Silmaril.X86.AluOp.cmp x y) .ne =
      some (!decide (x = y)) := by
  have := eval_ne_sub x y
  simp only [Silmaril.X86.Ext.AluOp.flagsN] at *
  rw [this]
  have e : (x - y = 0#64) ↔ (x = y) :=
    ⟨fun h => by have := congrArg (· + y) h; simpa using this, fun h => by subst h; simp⟩
  simp only [decide_eq_decide.mpr e]

theorem and100 {fl : BitVec 64} (h : fl.getLsbD 8 = false) :
    (BitVec.setWidth 32 fl &&& 256#32) = 0#32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat,
    show (256 : Nat) = 2 ^ 8 from rfl, Nat.testBit_two_pow]
  by_cases h8 : i = 8
  · subst h8
    have h' : fl[8] = false := by rw [← BitVec.getLsbD_eq_getElem]; exact h
    simp [h']
  · simp [Ne.symm h8]

theorem msb_small {k : Nat} (hk : k < 2 ^ 31) : (BitVec.ofNat 32 k).msb = false := by
  rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- **`rpl_fclose`** (`0x42b0`) on a stream open for reading, with no error, not on descriptor 1
(standard input included): closed, nothing written, returns 0. -/
theorem sha_rplFclose_in' {E : Env} {W : World} {b lb : Word} (I : CloseImps E W b lb) (hls : ImpOk W
      (lb + 0x11b2a0#64) (nm "lseek") (lseekStep E W)) {Q : PState → Prop}
    {s : PState} (hrip : s.m.core.rip = b + 0x42b0#64) (habi : AbiEntry s.m.core s.m.memory)
    (hroom : Room W s.m.memory (s.m.core.read .rsp) 256) (hlo : E.S.lo + 256 ≤ (s.m.core.read .rsp).toNat)
    (hd : s.g.done = none) (hm : ShaMemC b lb s.m.memory)
    {st : St} (hf : E.S.file s.m.memory (s.m.core.read .rdi) st) (hr : st.reading = true)
    (he : st.err = false) (hfd : st.fd ≠ 1) (hfd' : st.fd < 2 ^ 31)
    (k : ∀ t, AbiReturn s.m.core s.m.memory t.m.core →
      Keeps (fun a => W.Kept a ∨ (s.m.core.read .rsp).toNat ≤ a) s.m.memory t.m.memory →
      t.g.out = s.g.out → t.g.jobs = s.g.jobs → t.g.atexit = s.g.atexit → t.g.done = none →
      t.g.inp = s.g.inp → t.g.err = s.g.err →
      (t.g.allocs = s.g.allocs ∧ t.g.heap = s.g.heap ∧ t.g.files = s.g.files) →
      low32 (t.m.core.read .rax) = 0#32 → OK E s t.m.memory →
      t.m.core.fsBase = s.m.core.fsBase → PermKept s t.m.memory → LibK E W s.m.memory t.m.memory → MustQ W Q t) :
    MustQ W Q s := by
  have hin : ∀ n, n < 0xa188 → W.InImage (b + BitVec.ofNat 64 n).toNat := fun n hn => sha_in' I.img I.hb hn
  have hsp := hroom.1
  have hsp2 := hroom.2.1
  have hal := habi.aligned
  have hsv : ∀ p ∈ sv4 s, p.1 ≤ 32 ∧ 32 ≤ 40 := by
    intro p hp
    simp only [sv4, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> simp
  have hal40 : ((s.m.core.read .rsp).toNat - 40) % 16 = 0 := by omega
  refine prologue4 (shaMemC_keep I.img I.hb) shaC_listing_ok.2.1 rfl rfl rfl rfl rfl rfl rfl
    (fun k hk => img_off I.img I.hb (by omega)) (fun m h => h.rplFclose) hrip hroom (by decide) hd hm ?_
  intro u hB hrip1 hrbx hrdi hrbp hr12 hr13 hr14 hr15 hg hbytes hreg
  have hloc : ∀ f' st', E.S.file s.m.memory f' st' → E.S.file u.m.memory f' st' := fun f' st' h =>
    (E.S.local_ _ _ _ _ (fun a ha => ⟨hbytes a (Or.inl (by have := E.S.foot_lo _ _ _ _ h ha; omega)),
      fun acc => by simp only [Memory.permits, hreg]⟩) h).1
  have hu8 : E.S.lo ≤ (u.m.core.read .rsp - 8#64).toNat := by
    rw [hB.rsp, sub_toNat (k := 8) (by rw [sub_toNat (by omega) (by decide)]; omega) (by decide),
      sub_toNat (by omega) (by decide)]; omega
  have hLu : LibK E W s.m.memory u.m.memory := (LibK.refl E W _).high fun a ha =>
    ⟨hbytes a (Or.inl (by omega)), fun acc => by simp only [Memory.permits, hreg]⟩
  -- fileno (f)
  refine body_call (shaMemC_keep I.img I.hb) hB (by decide) (by decide) hsv hal40 I.lz
    (o := 16) (so := 0x180) (pb := b + 0x23c0#64) (fp := fun _ => False)
    shaC_listing_ok.2.1 rfl (by rw [hrip1]; exact img_off I.img I.hb (by decide)) (fun m h => h.rplFclose)
    hrip1 shaC_listing_ok.1 rfl rfl (by simp only [BitVec.add_assoc]; rfl)
    (img_off I.img I.hb (by decide)) (img_off I.img I.hb (by decide)) (fun m h => h.plt)
    (fun m h => by
      rw [show b + 0x23c0#64 + BitVec.ofNat 64 (0x180 + 4 + 6) + BitVec.signExtend 64 0x794e#32 = b + 0x9e98#64 by
        simp only [BitVec.add_assoc]; rfl]
      exact h.fileno)
    I.fileno.1 I.fileno.2.1 I.fileno.2.2.1 (fun r h => (impOk_fn I.fileno _ r).1 h)
    (fun he => ⟨he, st, by rw [callEntry_mem, callEntry_read _ _ _ (by decide), hrdi]; exact file_push (hloc _ _ hf) hu8⟩)
    (fun v hv => ⟨hv.1.1, hv.1.2.2.1, by simpa [callEntry] using hv.1.2.1, by rw [hv.2.1]; exact hB.done⟩)
    (fun x h => h.elim) (fun x h => h.elim) ?_
  intro v hv hB2 hrip2 hrsp2 hcs2
  have hL2 : LibK E W s.m.memory v.m.memory := hLu.call0 hu8 hv.1
  obtain ⟨-, hgv, hok2, hfdf⟩ := hv
  have hfE2 := file_push (v := b + 0x42b0#64 + BitVec.ofNat 64 (16 + 5)) (hloc _ _ hf) hu8
  have hfdv : BitVec.setWidth 32 (v.m.core.read .rax) = BitVec.ofNat 32 st.fd :=
    hfdf st (by rw [callEntry_mem, callEntry_read _ _ _ (by decide), hrdi]; exact hfE2)
  have hf2 : E.S.file v.m.memory (s.m.core.read .rdi) st :=
    hok2 _ st (by simp) (by rw [callEntry_mem]; exact hfE2)
  have hO2 : OK E s v.m.memory := fun f' st' hne h =>
    hok2 _ st' (by simp) (by rw [callEntry_mem]; exact file_push (hloc _ _ h) hu8)
  have hrbx2 : v.m.core.read .rbx = s.m.core.read .rdi := by
    rw [hcs2 .rbx (by simp [Silmaril.X86.sysv64_calleeSaved]), hrbx]
  have hg2 : v.g = s.g := by rw [hgv]; simp only [callEntry_g]; exact hg
  have h14_2 : v.m.core.read .r14 = s.m.core.read .r14 := by
    rw [hcs2 .r14 (by simp [Silmaril.X86.sysv64_calleeSaved]), hr14]
  have h15_2 : v.m.core.read .r15 = s.m.core.read .r15 := by
    rw [hcs2 .r15 (by simp [Silmaril.X86.sysv64_calleeSaved]), hr15]
  have hs : Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.logicFlagsN (andD (BitVec.ofNat 32 st.fd) (BitVec.ofNat 32 st.fd)))
      .s = some false := by rw [eval_s_testD, msb_small hfd']
  refine must_listed (o := 21) shaC_listing_ok.2.1 rfl hB2.done (by rw [hrip2]; exact img_off I.img I.hb (by decide))
    hB2.mem.rplFclose (by rw [hrip2]) ?_
  xstep [hrip2]
  refine must_listed (o := 24) shaC_listing_ok.2.1 rfl hB2.done (hin _ (by decide)) hB2.mem.rplFclose (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 26) shaC_listing_ok.2.1 rfl hB2.done (hin _ (by decide)) hB2.mem.rplFclose (by rw [ripadd]) ?_
  xstep [hfdv, hs]
  refine must_gen (fun u => Body W (ShaMemC b lb) s u 40 256 (sv4 s) ∧ u.m.core.rip = b + 0x42cc#64 ∧
      u.m.core.read .rdi = s.m.core.read .rdi ∧ u.m.core.read .rbx = s.m.core.read .rdi ∧
      u.m.core.read .rsp = v.m.core.read .rsp ∧ u.g = s.g ∧ E.S.file u.m.memory (s.m.core.read .rdi) st ∧
      u.m.core.read .r14 = s.m.core.read .r14 ∧ u.m.core.read .r15 = s.m.core.read .r15 ∧ OK E s u.m.memory ∧ LibK E W s.m.memory u.m.memory)
    ?_ ?_
  · exact ⟨hB2.of_eq rfl (by simp) rfl rfl, rfl, by simp [hrbx2], by simp [hrbx2], by simp, hg2, hf2,
      by simp [h14_2], by simp [h15_2], hO2, hL2⟩
  rintro v2 ⟨hB2', hrip2', hrdi2', hrbx2', hrsp2', hg2', hf2', h14_2', h15_2', hO2', hL2'⟩
  -- __freading (f)
  have hv8 : E.S.lo ≤ (v2.m.core.read .rsp - 8#64).toNat := by rw [hrsp2', hrsp2]; exact hu8
  refine body_call (shaMemC_keep I.img I.hb) hB2' (by decide) (by decide) hsv hal40 I.lz
    (o := 28) (so := 0x110) (pb := b + 0x23c0#64) (fp := fun _ => False)
    shaC_listing_ok.2.1 rfl (by rw [hrip2']; exact hin _ (by decide)) (fun m h => h.rplFclose)
    (by rw [hrip2', ripadd]) shaC_listing_ok.1 rfl rfl (by simp only [BitVec.add_assoc]; rfl)
    (img_off I.img I.hb (by decide)) (img_off I.img I.hb (by decide)) (fun m h => h.plt)
    (fun m h => by
      rw [show b + 0x23c0#64 + BitVec.ofNat 64 (0x110 + 4 + 6) + BitVec.signExtend 64 0x7986#32 = b + 0x9e60#64 by
        simp only [BitVec.add_assoc]; rfl]
      exact h.freading)
    I.freading.1 I.freading.2.1 I.freading.2.2.1 (fun r h => (impOk_fn I.freading _ r).1 h)
    (fun he => ⟨he, st, by rw [callEntry_mem, callEntry_read _ _ _ (by decide), hrdi2']; exact file_push hf2' hv8⟩)
    (fun w hw => ⟨hw.1.1, hw.1.2.2.1, by simpa [callEntry] using hw.1.2.1, by rw [hw.2.1]; exact hB2'.done⟩)
    (fun x h => h.elim) (fun x h => h.elim) ?_
  intro v3 hv3 hB3 hrip3 hrsp3 hcs3
  have hL3 : LibK E W s.m.memory v3.m.memory := hL2'.call0 hv8 hv3.1
  obtain ⟨-, hgv3, hok3, hrd3⟩ := hv3
  have hfE3 := file_push (v := b + 0x42b0#64 + BitVec.ofNat 64 (28 + 5)) hf2' hv8
  have hnz3 : BitVec.setWidth 32 (v3.m.core.read .rax) ≠ 0#32 := fun h =>
    absurd ((hrd3 st (by rw [callEntry_mem, callEntry_read _ _ _ (by decide), hrdi2']; exact hfE3)).1 h) (by rw [hr]; decide)
  have hf3 : E.S.file v3.m.memory (s.m.core.read .rdi) st := hok3 _ st (by simp) (by rw [callEntry_mem]; exact hfE3)
  have hO3 : OK E s v3.m.memory := fun f' st' hne h =>
    hok3 _ st' (by simp) (by rw [callEntry_mem]; exact file_push (hO2' f' st' hne h) hv8)
  have hrbx3 : v3.m.core.read .rbx = s.m.core.read .rdi := by
    rw [hcs3 .rbx (by simp [Silmaril.X86.sysv64_calleeSaved]), hrbx2']
  have hg3 : v3.g = s.g := by rw [hgv3]; simp only [callEntry_g]; exact hg2'
  have hne3 : Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.logicFlagsN
      (andD (BitVec.setWidth 32 (v3.m.core.read .rax)) (BitVec.setWidth 32 (v3.m.core.read .rax)))) .ne = some true := by
    rw [eval_ne_testD]; simp [hnz3]
  refine must_listed (o := 33) shaC_listing_ok.2.1 rfl hB3.done (by rw [hrip3]; exact img_off I.img I.hb (by decide))
    hB3.mem.rplFclose (by rw [hrip3]) ?_
  xstep [hrip3]
  refine must_listed (o := 35) shaC_listing_ok.2.1 rfl hB3.done (hin _ (by decide)) hB3.mem.rplFclose (by rw [ripadd]) ?_
  xstep [hne3]
  refine must_listed (o := 104) shaC_listing_ok.2.1 rfl hB3.done (hin _ (by decide)) hB3.mem.rplFclose (by rw [ripadd]) ?_
  xstep []
  refine must_gen (fun u => Body W (ShaMemC b lb) s u 40 256 (sv4 s) ∧ u.m.core.rip = b + 0x431b#64 ∧
      u.m.core.read .rdi = s.m.core.read .rdi ∧ u.m.core.read .rbx = s.m.core.read .rdi ∧
      u.m.core.read .rsp = v3.m.core.read .rsp ∧ u.g = s.g ∧ E.S.file u.m.memory (s.m.core.read .rdi) st ∧
      u.m.core.read .r14 = s.m.core.read .r14 ∧ u.m.core.read .r15 = s.m.core.read .r15 ∧ OK E s u.m.memory ∧ LibK E W s.m.memory u.m.memory)
    ?_ ?_
  · exact ⟨hB3.of_eq rfl (by simp) rfl rfl, rfl, by simp [hrbx3], by simp [hrbx3], by simp, hg3, hf3,
      by simp [hcs3 .r14 (by simp [Silmaril.X86.sysv64_calleeSaved]), h14_2'],
      by simp [hcs3 .r15 (by simp [Silmaril.X86.sysv64_calleeSaved]), h15_2'], hO3, hL3⟩
  rintro v4 ⟨hB4, hrip4, hrdi4, hrbx4, hrsp4, hg4, hf4, h14_4, h15_4, hO4, hL4⟩
  -- fileno (f), again
  have hv8' : E.S.lo ≤ (v4.m.core.read .rsp - 8#64).toNat := by rw [hrsp4, hrsp3, hrsp2', hrsp2]; exact hu8
  refine body_call (shaMemC_keep I.img I.hb) hB4 (by decide) (by decide) hsv hal40 I.lz
    (o := 107) (so := 0x180) (pb := b + 0x23c0#64) (fp := fun _ => False)
    shaC_listing_ok.2.1 rfl (by rw [hrip4]; exact hin _ (by decide)) (fun m h => h.rplFclose)
    (by rw [hrip4, ripadd]) shaC_listing_ok.1 rfl rfl (by simp only [BitVec.add_assoc]; rfl)
    (img_off I.img I.hb (by decide)) (img_off I.img I.hb (by decide)) (fun m h => h.plt)
    (fun m h => by
      rw [show b + 0x23c0#64 + BitVec.ofNat 64 (0x180 + 4 + 6) + BitVec.signExtend 64 0x794e#32 = b + 0x9e98#64 by
        simp only [BitVec.add_assoc]; rfl]
      exact h.fileno)
    I.fileno.1 I.fileno.2.1 I.fileno.2.2.1 (fun r h => (impOk_fn I.fileno _ r).1 h)
    (fun he => ⟨he, st, by rw [callEntry_mem, callEntry_read _ _ _ (by decide), hrdi4]; exact file_push hf4 hv8'⟩)
    (fun w hw => ⟨hw.1.1, hw.1.2.2.1, by simpa [callEntry] using hw.1.2.1, by rw [hw.2.1]; exact hB4.done⟩)
    (fun x h => h.elim) (fun x h => h.elim) ?_
  intro v5 hv5 hB5 hrip5 hrsp5 hcs5
  have hL5 : LibK E W s.m.memory v5.m.memory := hL4.call0 hv8' hv5.1
  obtain ⟨-, hgv5, hok5, -⟩ := hv5
  have hfE5 := file_push (v := b + 0x42b0#64 + BitVec.ofNat 64 (107 + 5)) hf4 hv8'
  have hf5 : E.S.file v5.m.memory (s.m.core.read .rdi) st := hok5 _ st (by simp) (by rw [callEntry_mem]; exact hfE5)
  have hO5 : OK E s v5.m.memory := fun f' st' hne h =>
    hok5 _ st' (by simp) (by rw [callEntry_mem]; exact file_push (hO4 f' st' hne h) hv8')
  have hrbx5 : v5.m.core.read .rbx = s.m.core.read .rdi := by
    rw [hcs5 .rbx (by simp [Silmaril.X86.sysv64_calleeSaved]), hrbx4]
  have hg5 : v5.g = s.g := by rw [hgv5]; simp only [callEntry_g]; exact hg4
  refine must_listed (o := 112) shaC_listing_ok.2.1 rfl hB5.done (by rw [hrip5]; exact img_off I.img I.hb (by decide))
    hB5.mem.rplFclose (by rw [hrip5]) ?_
  xstep [hrip5]
  refine must_listed (o := 114) shaC_listing_ok.2.1 rfl hB5.done (hin _ (by decide)) hB5.mem.rplFclose (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 119) shaC_listing_ok.2.1 rfl hB5.done (hin _ (by decide)) hB5.mem.rplFclose (by rw [ripadd]) ?_
  xstep []
  refine must_gen (fun u => Body W (ShaMemC b lb) s u 40 256 (sv4 s) ∧ u.m.core.rip = b + 0x4329#64 ∧
      u.m.core.read .rbx = s.m.core.read .rdi ∧
      u.m.core.read .rsp = v5.m.core.read .rsp ∧ u.g = s.g ∧ E.S.file u.m.memory (s.m.core.read .rdi) st ∧
      u.m.core.read .r14 = s.m.core.read .r14 ∧ u.m.core.read .r15 = s.m.core.read .r15 ∧ OK E s u.m.memory ∧ LibK E W s.m.memory u.m.memory)
    ?_ ?_
  · exact ⟨hB5.of_eq rfl (by simp) rfl rfl, rfl, by simp [hrbx5], by simp, hg5, hf5,
      by simp [hcs5 .r14 (by simp [Silmaril.X86.sysv64_calleeSaved]), h14_4],
      by simp [hcs5 .r15 (by simp [Silmaril.X86.sysv64_calleeSaved]), h15_4], hO5, hL5⟩
  rintro v6 ⟨hB6, hrip6, hrbx6, hrsp6, hg6, hf6, h14_6, h15_6, hO6, hL6⟩
  -- lseek (fd, 0, SEEK_CUR)
  have hv86 : E.S.lo ≤ (v6.m.core.read .rsp - 8#64).toNat := by rw [hrsp6, hrsp5, hrsp4, hrsp3, hrsp2', hrsp2]; exact hu8
  refine body_call (shaMemC_keep I.img I.hb) hB6 (by decide) (by decide) hsv hal40 I.lz
    (o := 121) (so := 0x300) (pb := b + 0x23c0#64) (fp := fun _ => False)
    shaC_listing_ok.2.1 rfl (by rw [hrip6]; exact hin _ (by decide)) (fun m h => h.rplFclose)
    (by rw [hrip6, ripadd]) shaC_listing_ok.1 rfl rfl (by simp only [BitVec.add_assoc]; rfl)
    (img_off I.img I.hb (by decide)) (img_off I.img I.hb (by decide)) (fun m h => h.plt)
    (fun m h => by
      rw [show b + 0x23c0#64 + BitVec.ofNat 64 (0x300 + 4 + 6) + BitVec.signExtend 64 0x788e#32 = b + 0x9f58#64 by
        simp only [BitVec.add_assoc]; rfl]
      exact h.lseek)
    hls.1 hls.2.1 hls.2.2.1 (fun r h => (impOk_fn hls _ r).1 h)
    (fun he => he)
    (fun w hw => ⟨hw.1.1, hw.1.2.2.1, by simpa [callEntry] using hw.1.2.1, by rw [hw.2.2.1]; exact hB6.done⟩)
    (fun x h => h.elim) (fun x h => h.elim) ?_
  intro v7 hv7 hB7 hrip7 hrsp7 hcs7
  have hL7 : LibK E W s.m.memory v7.m.memory := hL6.call0 hv86 hv7.1
  obtain ⟨-, -, hgv7, hok7⟩ := hv7
  have hfE7 := file_push (v := b + 0x42b0#64 + BitVec.ofNat 64 (121 + 5)) hf6 hv86
  have hf7 : E.S.file v7.m.memory (s.m.core.read .rdi) st := hok7 _ st (by simp) (by rw [callEntry_mem]; exact hfE7)
  have hO7 : OK E s v7.m.memory := fun f' st' hne h =>
    hok7 _ st' (by simp) (by rw [callEntry_mem]; exact file_push (hO6 f' st' hne h) hv86)
  have hrbx7 : v7.m.core.read .rbx = s.m.core.read .rdi := by
    rw [hcs7 .rbx (by simp [Silmaril.X86.sysv64_calleeSaved]), hrbx6]
  have hg7 : v7.g = s.g := by rw [hgv7]; simp only [callEntry_g]; exact hg6
  have h14_7 : v7.m.core.read .r14 = s.m.core.read .r14 := by
    rw [hcs7 .r14 (by simp [Silmaril.X86.sysv64_calleeSaved]), h14_6]
  have h15_7 : v7.m.core.read .r15 = s.m.core.read .r15 := by
    rw [hcs7 .r15 (by simp [Silmaril.X86.sysv64_calleeSaved]), h15_6]
  refine must_listed (o := 126) shaC_listing_ok.2.1 rfl hB7.done (by rw [hrip7]; exact img_off I.img I.hb (by decide))
    hB7.mem.rplFclose (by rw [hrip7]) ?_
  xstep [hrip7]
  refine must_listed (o := 130) shaC_listing_ok.2.1 rfl hB7.done (hin _ (by decide)) hB7.mem.rplFclose (by rw [ripadd]) ?_
  -- the two outcomes of lseek; both end in the tail
  have tail : ∀ {st' : St} {w : PState}, Body W (ShaMemC b lb) s w 40 256 (sv4 s) → w.m.core.rip = b + 17204#64 →
      w.m.core.read .rbx = s.m.core.read .rdi → w.m.core.read .r14 = s.m.core.read .r14 →
      w.m.core.read .r15 = s.m.core.read .r15 → E.S.file w.m.memory (s.m.core.read .rdi) st' → st'.err = false →
      st'.fd = st.fd → w.g = { s.g with blocks := w.g.blocks } → OK E s w.m.memory →
      LibK E W s.m.memory w.m.memory → MustQ W Q w := by
    intro st' w hBw hripw hrbxw h14w h15w hfw hew hfdw hgw hOw hLw
    refine rplTail I habi hBw hripw hrbxw h14w h15w hfw hew (fun h => absurd (hfdw.symm.trans h) hfd) hLw ?_
    intro t habiT hkT hoT hjT haT hdT hiT heT hcT hzT hokT hfT hpT hLT
    refine k t habiT hkT ?_ (by rw [hjT, hgw]) (by rw [haT, hgw]) hdT (by rw [hiT, hgw]) (by rw [heT, hgw])
      (by rw [hcT.1, hcT.2.1, hcT.2.2, hgw]; exact ⟨rfl, rfl, rfl⟩) hzT
      (fun f' st'' hne h => hokT f' st'' hne (hOw f' st'' hne h)) hfT hpT hLT
    rw [hoT, hgw, hfdw]; simp [hfd]
  by_cases hm1 : v7.m.core.read .rax = 18446744073709551615#64
  · xstep [eval_ne_cmp, hm1]
    exact tail (st' := st) (hB7.of_eq rfl rfl rfl rfl) rfl hrbx7 h14_7 h15_7 hf7 he rfl (by rw [hg7]) hO7 hL7
  · xstep [eval_ne_cmp, hm1]
    refine must_listed (o := 37) shaC_listing_ok.2.1 rfl hB7.done (hin _ (by decide)) hB7.mem.rplFclose (by rw [ripadd]) ?_
    xstep []
    refine must_gen (fun u => Body W (ShaMemC b lb) s u 40 256 (sv4 s) ∧ u.m.core.rip = b + 0x42d8#64 ∧
        u.m.core.read .rdi = s.m.core.read .rdi ∧ u.m.core.read .rbx = s.m.core.read .rdi ∧
        u.m.core.read .rsp = v7.m.core.read .rsp ∧ u.g = s.g ∧ E.S.file u.m.memory (s.m.core.read .rdi) st ∧
        u.m.core.read .r14 = s.m.core.read .r14 ∧ u.m.core.read .r15 = s.m.core.read .r15 ∧ OK E s u.m.memory ∧ LibK E W s.m.memory u.m.memory)
      ?_ ?_
    · exact ⟨hB7.of_eq rfl (by simp) rfl rfl, rfl, by simp [hrbx7], by simp [hrbx7], by simp, hg7, hf7,
        by simp [h14_7], by simp [h15_7], hO7, hL7⟩
    rintro v8 ⟨hB8, hrip8, hrdi8, hrbx8, hrsp8, hg8, hf8, h14_8, h15_8, hO8, hL8⟩
    have hv88 : E.S.lo ≤ (v8.m.core.read .rsp - 8#64).toNat := by
      rw [hrsp8, hrsp7, hrsp6, hrsp5, hrsp4, hrsp3, hrsp2', hrsp2]; exact hu8
    refine body_call (shaMemC_keep I.img I.hb) hB8 (by decide) (by decide) hsv hal40 I.lz
      (o := 40) (so := 0x110) (pb := b + 0x23c0#64) (fp := fun _ => False)
      shaC_listing_ok.2.1 rfl (by rw [hrip8]; exact hin _ (by decide)) (fun m h => h.rplFclose)
      (by rw [hrip8, ripadd]) shaC_listing_ok.1 rfl rfl (by simp only [BitVec.add_assoc]; rfl)
      (img_off I.img I.hb (by decide)) (img_off I.img I.hb (by decide)) (fun m h => h.plt)
      (fun m h => by
        rw [show b + 0x23c0#64 + BitVec.ofNat 64 (0x110 + 4 + 6) + BitVec.signExtend 64 0x7986#32 = b + 0x9e60#64 by
          simp only [BitVec.add_assoc]; rfl]
        exact h.freading)
      I.freading.1 I.freading.2.1 I.freading.2.2.1 (fun r h => (impOk_fn I.freading _ r).1 h)
      (fun he => ⟨he, st, by rw [callEntry_mem, callEntry_read _ _ _ (by decide), hrdi8]; exact file_push hf8 hv88⟩)
      (fun w hw => ⟨hw.1.1, hw.1.2.2.1, by simpa [callEntry] using hw.1.2.1, by rw [hw.2.1]; exact hB8.done⟩)
      (fun x h => h.elim) (fun x h => h.elim) ?_
    intro v9 hv9 hB9 hrip9 hrsp9 hcs9
    have hL9 : LibK E W s.m.memory v9.m.memory := hL8.call0 hv88 hv9.1
    obtain ⟨-, hgv9, hok9, hrd9⟩ := hv9
    have hfE9 := file_push (v := b + 0x42b0#64 + BitVec.ofNat 64 (40 + 5)) hf8 hv88
    have hnz9 : BitVec.setWidth 32 (v9.m.core.read .rax) ≠ 0#32 := fun h =>
      absurd ((hrd9 st (by rw [callEntry_mem, callEntry_read _ _ _ (by decide), hrdi8]; exact hfE9)).1 h) (by rw [hr]; decide)
    have hf9 : E.S.file v9.m.memory (s.m.core.read .rdi) st := hok9 _ st (by simp) (by rw [callEntry_mem]; exact hfE9)
    have hO9 : OK E s v9.m.memory := fun f' st' hne h =>
      hok9 _ st' (by simp) (by rw [callEntry_mem]; exact file_push (hO8 f' st' hne h) hv88)
    have hrbx9 : v9.m.core.read .rbx = s.m.core.read .rdi := by
      rw [hcs9 .rbx (by simp [Silmaril.X86.sysv64_calleeSaved]), hrbx8]
    have hg9 : v9.g = s.g := by rw [hgv9]; simp only [callEntry_g]; exact hg8
    have hne9 : Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.logicFlagsN
        (andD (BitVec.setWidth 32 (v9.m.core.read .rax)) (BitVec.setWidth 32 (v9.m.core.read .rax)))) .ne = some true := by
      rw [eval_ne_testD]; simp [hnz9]
    obtain ⟨fl, hfl, -, -, hfl8⟩ := E.S.flags _ _ _ hf9
    have hz100 : (BitVec.setWidth 32 fl &&& 256#32) = 0#32 := and100 hfl8
    refine must_listed (o := 45) shaC_listing_ok.2.1 rfl hB9.done (by rw [hrip9]; exact img_off I.img I.hb (by decide))
      hB9.mem.rplFclose (by rw [hrip9]) ?_
    xstep [hrip9]
    refine must_listed (o := 47) shaC_listing_ok.2.1 rfl hB9.done (hin _ (by decide)) hB9.mem.rplFclose (by rw [ripadd]) ?_
    xstep [hne9]
    refine must_listed (o := 160) shaC_listing_ok.2.1 rfl hB9.done (hin _ (by decide)) hB9.mem.rplFclose (by rw [ripadd]) ?_
    xstep [ofReg_addr0, hrbx9, hfl]
    have he0 : Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.logicFlagsN (andD (BitVec.setWidth 32 fl) 256#32)) .e =
        some true := by
      rw [show andD (BitVec.setWidth 32 fl) 256#32 = 0#32 from hz100]; rfl
    refine must_listed (o := 166) shaC_listing_ok.2.1 rfl hB9.done (hin _ (by decide)) hB9.mem.rplFclose (by rw [ripadd]) ?_
    xstep [he0]
    refine must_listed (o := 49) shaC_listing_ok.2.1 rfl hB9.done (hin _ (by decide)) hB9.mem.rplFclose (by rw [ripadd]) ?_
    xstep []
    refine must_gen (fun u => Body W (ShaMemC b lb) s u 40 256 (sv4 s) ∧ u.m.core.rip = b + 0x42e4#64 ∧
        u.m.core.read .rdi = s.m.core.read .rdi ∧ u.m.core.read .rbx = s.m.core.read .rdi ∧
        u.m.core.read .rsp = v9.m.core.read .rsp ∧ u.g = s.g ∧ E.S.file u.m.memory (s.m.core.read .rdi) st ∧
        u.m.core.read .r14 = s.m.core.read .r14 ∧ u.m.core.read .r15 = s.m.core.read .r15 ∧ OK E s u.m.memory ∧ LibK E W s.m.memory u.m.memory)
      ?_ ?_
    · exact ⟨hB9.of_eq rfl (by simp) rfl rfl, rfl, by simp [hrbx9], by simp [hrbx9], by simp, hg9, hf9,
        by simp [hcs9 .r14 (by simp [Silmaril.X86.sysv64_calleeSaved]), h14_8],
        by simp [hcs9 .r15 (by simp [Silmaril.X86.sysv64_calleeSaved]), h15_8], hO9, hL9⟩
    rintro v10 ⟨hB10, hrip10, hrdi10, hrbx10, hrsp10, hg10, hf10, h14_10, h15_10, hO10, hL10⟩
    have hv810 : E.S.lo ≤ (v10.m.core.read .rsp - 8#64).toNat := by
      rw [hrsp10, hrsp9, hrsp8, hrsp7, hrsp6, hrsp5, hrsp4, hrsp3, hrsp2', hrsp2]; exact hu8
    refine body_call (shaMemC_keep I.img I.hb) hB10 (by decide) (by decide) hsv hal40 I.lz
      (o := 52) (so := 0x1e0) (pb := b + 0x23c0#64) (fp := fun _ => False)
      shaC_listing_ok.2.1 rfl (by rw [hrip10]; exact hin _ (by decide)) (fun m h => h.rplFclose)
      (by rw [hrip10, ripadd]) shaC_listing_ok.1 rfl rfl (by simp only [BitVec.add_assoc]; rfl)
      (img_off I.img I.hb (by decide)) (img_off I.img I.hb (by decide)) (fun m h => h.plt)
      (fun m h => by
        rw [show b + 0x23c0#64 + BitVec.ofNat 64 (0x1e0 + 4 + 6) + BitVec.signExtend 64 0x791e#32 = b + 0x9ec8#64 by
          simp only [BitVec.add_assoc]; rfl]
        exact h.fflush)
      I.fflush.1 I.fflush.2.1 I.fflush.2.2.1 (fun r h => (impOk_fn I.fflush _ r).1 h)
      (fun he => ⟨he, st, by rw [callEntry_mem, callEntry_read _ _ _ (by decide), hrdi10]; exact file_push hf10 hv810⟩)
      (fun w hw => ⟨hw.1.1, hw.1.2.2.1, by simpa [callEntry] using hw.1.2.1, hw.2.1.2.2.1⟩)
      (fun x h => h.elim) (fun x h => h.elim) ?_
    intro v11 hv11 hB11 hrip11 hrsp11 hcs11
    have hL11 : LibK E W s.m.memory v11.m.memory := hL10.call0 hv810 hv11.1
    obtain ⟨-, ⟨hj11, ha11, hd11, hi11, herr11, hal11, hhp11, hfi11⟩, hok11, hfl11⟩ := hv11
    have hfE11 := file_push (v := b + 0x42b0#64 + BitVec.ofNat 64 (52 + 5)) hf10 hv810
    have hfl := hfl11 st (by rw [callEntry_mem, callEntry_read _ _ _ (by decide), hrdi10]; exact hfE11)
    obtain ⟨ho11, hf11, hz11⟩ := hfl.2 (by omega)
    have hz11' : BitVec.setWidth 32 (v11.m.core.read .rax) = 0#32 := hz11 he
    have hO11 : OK E s v11.m.memory := fun f' st' hne h =>
      hok11 _ st' (by rw [callEntry_read _ _ _ (by decide), hrdi10]; simpa using hne)
        (by rw [callEntry_mem]; exact file_push (hO10 f' st' hne h) hv810)
    have hrbx11 : v11.m.core.read .rbx = s.m.core.read .rdi := by
      rw [hcs11 .rbx (by simp [Silmaril.X86.sysv64_calleeSaved]), hrbx10]
    have hg11 : v11.g = { s.g with blocks := v11.g.blocks } := by
      have hjs : v11.g.jobs = s.g.jobs := by rw [hj11]; simp only [callEntry_g]; rw [hg10]
      have has : v11.g.atexit = s.g.atexit := by rw [ha11]; simp only [callEntry_g]; rw [hg10]
      have his : v11.g.inp = s.g.inp := by rw [hi11]; simp only [callEntry_g]; rw [hg10]
      have hes : v11.g.err = s.g.err := by rw [herr11]; simp only [callEntry_g]; rw [hg10]
      have hos : v11.g.out = s.g.out := by rw [ho11]; simp only [callEntry_g]; rw [hg10]
      have hds : v11.g.done = s.g.done := by rw [hd11, hd]
      have hal : v11.g.allocs = s.g.allocs := by rw [hal11]; simp only [callEntry_g]; rw [hg10]
      have hhp : v11.g.heap = s.g.heap := by rw [hhp11]; simp only [callEntry_g]; rw [hg10]
      have hfi : v11.g.files = s.g.files := by rw [hfi11]; simp only [callEntry_g]; rw [hg10]
      cases h1 : v11.g; cases h2 : s.g; simp_all
    refine must_listed (o := 57) shaC_listing_ok.2.1 rfl hB11.done (by rw [hrip11]; exact img_off I.img I.hb (by decide))
      hB11.mem.rplFclose (by rw [hrip11]) ?_
    xstep [hrip11]
    refine must_listed (o := 59) shaC_listing_ok.2.1 rfl hB11.done (hin _ (by decide)) hB11.mem.rplFclose (by rw [ripadd]) ?_
    xstep [eval_e_testD, hz11']
    exact tail (st' := { st with buf := [] }) (hB11.of_eq rfl (by simp) rfl rfl) rfl (by simp [hrbx11])
      (by simp [hcs11 .r14 (by simp [Silmaril.X86.sysv64_calleeSaved]), h14_10])
      (by simp [hcs11 .r15 (by simp [Silmaril.X86.sysv64_calleeSaved]), h15_10])
      (by simpa [callEntry_read _ _ _ (show Reg.rdi ≠ .rsp by decide), hrdi10] using hf11) he rfl hg11 hO11 hL11


/-- `sha_rplFclose_in'` for a stream on a descriptor `≥ 3` (the form `digest_file` uses). -/
theorem sha_rplFclose_in {E : Env} {W : World} {b lb : Word} (I : CloseImps E W b lb) (hls : ImpOk W
      (lb + 0x11b2a0#64) (nm "lseek") (lseekStep E W)) {Q : PState → Prop}
    {s : PState} (hrip : s.m.core.rip = b + 0x42b0#64) (habi : AbiEntry s.m.core s.m.memory)
    (hroom : Room W s.m.memory (s.m.core.read .rsp) 256) (hlo : E.S.lo + 256 ≤ (s.m.core.read .rsp).toNat)
    (hd : s.g.done = none) (hm : ShaMemC b lb s.m.memory)
    {st : St} (hf : E.S.file s.m.memory (s.m.core.read .rdi) st) (hr : st.reading = true)
    (he : st.err = false) (hfd : 3 ≤ st.fd) (hfd' : st.fd < 2 ^ 31)
    (k : ∀ t, AbiReturn s.m.core s.m.memory t.m.core →
      Keeps (fun a => W.Kept a ∨ (s.m.core.read .rsp).toNat ≤ a) s.m.memory t.m.memory →
      t.g.out = s.g.out → t.g.jobs = s.g.jobs → t.g.atexit = s.g.atexit → t.g.done = none →
      t.g.inp = s.g.inp → t.g.err = s.g.err →
      (t.g.allocs = s.g.allocs ∧ t.g.heap = s.g.heap ∧ t.g.files = s.g.files) →
      low32 (t.m.core.read .rax) = 0#32 → OK E s t.m.memory →
      t.m.core.fsBase = s.m.core.fsBase → PermKept s t.m.memory → LibK E W s.m.memory t.m.memory → MustQ W Q t) :
    MustQ W Q s :=
  sha_rplFclose_in' I hls hrip habi hroom hlo hd hm hf hr he (by omega) hfd' k

end Silmaril.Elf.Link.Dyn.Sha256sum
