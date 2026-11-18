module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.Close

/-! # GNU `sha256sum`: `close_stream` on an output stream -/

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

theorem below_a1 {x sp : Nat} (h1 : sp - 524288 ≤ x) : sp - 48 - 524288 ≤ x :=
  Nat.le_trans (Nat.sub_le_sub_right (Nat.sub_le sp 48) _) h1
theorem below_a2 {x sp : Nat} (hx : ¬ sp - 48 ≤ x) : x < sp - 48 + 8 :=
  Nat.lt_of_lt_of_le (Nat.lt_of_not_le hx) (Nat.le_add_right _ _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- **`close_stream`** (`0x45c0`) on an output stream with no error, writes reliable: returns 0
having written the buffer (to the output if it is `stdout`). -/
theorem sha_closeStream_out {E : Env} {W : World} {b lb : Word} (I : CloseImps E W b lb) {Q : PState → Prop}
    {s : PState} (hrip : s.m.core.rip = b + 0x45c0#64) (habi : AbiEntry s.m.core s.m.memory)
    (hroom : Room W s.m.memory (s.m.core.read .rsp) 512) (hlo : E.S.lo + 512 ≤ (s.m.core.read .rsp).toNat)
    (hd : s.g.done = none) (hm : ShaMemC b lb s.m.memory) (hrel : W.reliable = true)
    {st : St} (hf : E.S.file s.m.memory (s.m.core.read .rdi) st) (hr : st.reading = false)
    (he : st.err = false) (hfd : st.fd < 2 ^ 31)
    (k : ∀ t, AbiReturn s.m.core s.m.memory t.m.core →
      Keeps (fun a => W.Kept a ∨ (s.m.core.read .rsp).toNat ≤ a) s.m.memory t.m.memory →
      t.g.out = s.g.out ++ (if st.fd = 1 then st.buf else []) → t.g.jobs = s.g.jobs →
      t.g.atexit = s.g.atexit → t.g.done = none → t.g.inp = s.g.inp → t.g.err = s.g.err →
      low32 (t.m.core.read .rax) = 0#32 → OK E s t.m.memory → PermKept s t.m.memory → MustQ W Q t) :
    MustQ W Q s := by
  have hin : ∀ n, n < 0xa188 → W.InImage (b + BitVec.ofNat 64 n).toNat := fun n hn => sha_in' I.img I.hb hn
  have hsp := hroom.1
  have hsp2 := hroom.2.1
  have hal := habi.aligned
  refine prologue4 (shaMemC_keep I.img I.hb) shaC_listing_ok.2.2.1 rfl rfl rfl rfl rfl rfl rfl
    (fun k hk => img_off I.img I.hb (by omega)) (fun m h => h.closeStream) hrip hroom (by decide) hd hm ?_
  intro u hB hrip1 hrbx hrdi hrbp hr12 hr13 hr14 hr15 hg hbytes hreg
  have hf1 : E.S.file u.m.memory (s.m.core.read .rdi) st :=
    (E.S.local_ _ _ _ _ (fun a ha => ⟨hbytes a (Or.inl (by have := E.S.foot_lo _ _ _ _ hf ha; omega)),
      fun acc => by simp only [Memory.permits, hreg]⟩) hf).1
  have hO1 : OK E s u.m.memory := fun f' st' _ h =>
    (E.S.local_ _ _ _ _ (fun a ha => ⟨hbytes a (Or.inl (by have := E.S.foot_lo _ _ _ _ h ha; omega)),
      fun acc => by simp only [Memory.permits, hreg]⟩) h).1
  have hsv : ∀ p ∈ sv4 s, p.1 ≤ 32 ∧ 32 ≤ 40 := by
    intro p hp
    simp only [sv4, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> simp
  have hal40 : ((s.m.core.read .rsp).toNat - 40) % 16 = 0 := by omega
  have hu8 : E.S.lo ≤ (u.m.core.read .rsp - 8#64).toNat := by
    rw [hB.rsp, sub_toNat (k := 8) (by rw [sub_toNat (by omega) (by decide)]; omega) (by decide),
      sub_toNat (by omega) (by decide)]; omega
  -- __fpending (f)
  refine body_call (shaMemC_keep I.img I.hb) hB (by decide) (by decide) hsv hal40 I.lz
    (o := 16) (so := 0x250) (pb := b + 0x23c0#64) (fp := fun _ => False)
    shaC_listing_ok.2.2.1 rfl (by rw [hrip1]; exact img_off I.img I.hb (by decide)) (fun m h => h.closeStream)
    hrip1 shaC_listing_ok.1 rfl rfl (by simp only [BitVec.add_assoc]; rfl)
    (img_off I.img I.hb (by decide)) (img_off I.img I.hb (by decide)) (fun m h => h.plt)
    (fun m h => by
      rw [show b + 0x23c0#64 + BitVec.ofNat 64 (0x250 + 4 + 6) + BitVec.signExtend 64 0x78e6#32 = b + 0x9f00#64 by
        simp only [BitVec.add_assoc]; rfl]
      exact h.fpending)
    I.fpending.1 I.fpending.2.1 I.fpending.2.2.1 (fun r h => (impOk_fn I.fpending _ r).1 h)
    (fun he => ⟨he, st, by rw [callEntry_mem, callEntry_read _ _ _ (by decide), hrdi]; exact file_push hf1 hu8⟩)
    (fun v hv => ⟨hv.1.1, hv.1.2.2.1, by simpa [callEntry] using hv.1.2.1,
      by rw [hv.2.1]; exact hB.done⟩)
    (fun x h => h.elim) (fun x h => h.elim) ?_
  intro v hv hB2 hrip2 hrsp2 hcs2
  obtain ⟨-, hgv, hok2, hfp⟩ := hv
  have hfE2 := file_push (v := b + 0x45c0#64 + BitVec.ofNat 64 (16 + 5)) hf1 hu8
  have hf2 : E.S.file v.m.memory (s.m.core.read .rdi) st := by
    have := (hfp st (by rw [callEntry_mem, callEntry_read _ _ _ (by decide), hrdi]; exact hfE2)).1
    rwa [callEntry_read _ _ _ (by decide), hrdi] at this
  have hrbx2 : v.m.core.read .rbx = s.m.core.read .rdi := by
    rw [hcs2 .rbx (by simp [Silmaril.X86.sysv64_calleeSaved]), hrbx]
  have hO2 : OK E s v.m.memory := fun f' st' hne h =>
    hok2 _ st' (by simp) (by rw [callEntry_mem]; exact file_push (hO1 f' st' hne h) hu8)
  obtain ⟨fl, hfl, -, hfl5, -⟩ := E.S.flags _ _ _ hf2
  refine must_listed (o := 21) shaC_listing_ok.2.2.1 rfl hB2.done (by rw [hrip2]; exact img_off I.img I.hb (by decide))
    hB2.mem.closeStream (by rw [hrip2]) ?_
  xstep [hrip2, hrbx2, hfl, ofReg_addr]
  refine must_listed (o := 24) shaC_listing_ok.2.2.1 rfl hB2.done (hin _ (by decide))
    hB2.mem.closeStream (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 27) shaC_listing_ok.2.2.1 rfl hB2.done (hin _ (by decide))
    hB2.mem.closeStream (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 30) shaC_listing_ok.2.2.1 rfl hB2.done (hin _ (by decide))
    hB2.mem.closeStream (by rw [ripadd]) ?_
  xstep []
  refine must_gen (fun u => Body W (ShaMemC b lb) s u 40 512 (sv4 s) ∧ u.m.core.rip = b + 0x45e2#64 ∧
      u.m.core.read .rdi = s.m.core.read .rdi ∧ u.m.core.read .rbx = s.m.core.read .rdi ∧
      BitVec.setWidth 32 (u.m.core.read .r12) = 0#32 ∧ u.m.core.read .rbp = s.m.core.read .rsp - 8#64 ∧
      u.m.core.read .r14 = s.m.core.read .r14 ∧ u.m.core.read .r15 = s.m.core.read .r15 ∧
      u.g = s.g ∧ E.S.file u.m.memory (s.m.core.read .rdi) st ∧ OK E s u.m.memory) ?_ ?_
  · refine ⟨hB2.of_eq rfl (by simp) rfl rfl, rfl, by simp [hrbx2], by simp [hrbx2], ?_, ?_, ?_, ?_, ?_, hf2, hO2⟩
    · simp [Silmaril.X86.Ext.AluOp.resultN]; exact and20 (hfl5.trans he)
    · simp [hcs2 .rbp (by simp [Silmaril.X86.sysv64_calleeSaved]), hrbp]
    · simp [hcs2 .r14 (by simp [Silmaril.X86.sysv64_calleeSaved]), hr14]
    · simp [hcs2 .r15 (by simp [Silmaril.X86.sysv64_calleeSaved]), hr15]
    · show v.g = s.g; rw [hgv]; simp only [callEntry_g]; exact hg
  rintro u2 ⟨hB3, hrip3, hrdi3, hrbx3, hr123, hrbp3, hr143, hr153, hg3, hf3, hO3⟩
  have hu2r : (u2.m.core.read .rsp).toNat = (s.m.core.read .rsp).toNat - 40 := by
    rw [hB3.rsp]; exact sub_toNat (by omega) (by decide)
  have hu28 : (u2.m.core.read .rsp - 8#64).toNat = (s.m.core.read .rsp).toNat - 48 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), hu2r]; omega
  have pw : u2.m.memory.Permitted .write (u2.m.core.read .rsp - 8#64).toNat 8 :=
    room_perm hB3.room (Or.inr rfl) (by omega) (by omega)
  have pr : u2.m.memory.Permitted .read (u2.m.core.read .rsp - 8#64).toNat 8 :=
    room_perm hB3.room (Or.inl rfl) (by omega) (by omega)
  -- the call of rpl_fclose
  refine must_listed (o := 34) shaC_listing_ok.2.2.1 rfl hB3.done (by rw [hrip3]; exact hin _ (by decide))
    hB3.mem.closeStream (by rw [hrip3, ripadd]) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem pw]
  xstep [hrip3]
  have hsp48 : u2.m.core.read .rsp - 8#64 = s.m.core.read .rsp - BitVec.ofNat 64 48 := by
    rw [hB3.rsp]; bv_omega
  have hroom' : Room W (pushMem u2.m.memory (u2.m.core.read .rsp) (b + 17895#64)) (u2.m.core.read .rsp - 8#64) 256 := by
    rw [hsp48]; exact (hB3.room.pushMem.down (d := 48) (by decide) (by decide)).mono (by decide)
  refine sha_rplFclose_out I (st := st) rfl
    (abiEntry_of (v := b + 17895#64) (by show (u2.m.core.read .rsp - 8#64).toNat % 16 = 8; rw [hu28]; omega)
      (by simpa using pushMem_read pr pw))
    (by simpa using hroom') (by show E.S.lo + 256 ≤ (u2.m.core.read .rsp - 8#64).toNat; rw [hu28]; omega) hB3.done
    (shaMemC_keep I.img I.hb _ _ hB3.mem (room_push_img hB3.room (by omega) (by omega))) hrel
    (by simpa [hrdi3] using file_push (v := b + 17895#64) hf3 (by rw [hu28]; omega)) hr he hfd ?_
  intro t habiT hkT hoT hjT haT hdT hiT heT hzT hOT hPT
  have hripT : t.m.core.rip = b + 17895#64 := by
    rw [habiT.pc]; exact retOf_of (by simpa using pushMem_read pr pw)
  have hrspT : t.m.core.read .rsp = u2.m.core.read .rsp := by
    rw [habiT.stack]; simp
  have hcsT : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, t.m.core.read r = u2.m.core.read r := by
    intro r hr
    rw [habiT.calleeSaved r hr]
    have : r ≠ .rsp := fun h => Silmaril.X86.sysv64_rsp_not_calleeSaved (h ▸ hr)
    simp [this]
  have hkU : Keeps (fun a => W.Kept a ∨ (s.m.core.read .rsp).toNat - 40 ≤ a) u2.m.memory t.m.memory := by
    refine (pushMem_keeps (fun x hx => ?_)).trans (hkT.mono fun x hx => ?_)
    · rcases hx with hx | hx
      · by_cases hc : (s.m.core.read .rsp).toNat - 512 ≤ x ∧ x < (s.m.core.read .rsp).toNat + 8
        · exact absurd hx (hB3.room.2.2 x hc.1 hc.2).2.2
        · rw [hu28]; omega
      · rw [hu28]; omega
    · rcases hx with hx | hx
      · exact Or.inl hx
      · right; show (u2.m.core.read .rsp - 8#64).toNat ≤ x; rw [hu28]; omega
  have hmT : ShaMemC b lb t.m.memory :=
    shaMemC_keep I.img I.hb _ _ hB3.mem (hkU.mono fun x hx => Or.inl (Or.inl hx))
  have hz12 : BitVec.setWidth 32 (t.m.core.read .r12) = 0#32 := by
    rw [hcsT .r12 (by simp [Silmaril.X86.sysv64_calleeSaved])]; exact hr123
  have hzax : BitVec.setWidth 32 (t.m.core.read .rax) = 0#32 := hzT
  have sv : ∀ p ∈ sv4 s, t.m.memory.readBytes ((s.m.core.read .rsp).toNat - p.1) 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [p.2]) := by
    intro p hp
    have h1 := (hsv p hp).1
    have h0 : 8 ≤ p.1 := by
      simp only [sv4, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> simp
    rw [hkU.readBytes (fun j hj => Or.inr (by omega))]
    exact hB3.saved p hp
  have q8 : ((u2.m.core.read .rsp).toNat + 8) % 18446744073709551616 = (s.m.core.read .rsp).toNat - 32 := by
    rw [hu2r]; omega
  have q16 : ((u2.m.core.read .rsp).toNat + 16) % 18446744073709551616 = (s.m.core.read .rsp).toNat - 24 := by
    rw [hu2r]; omega
  have q24 : ((u2.m.core.read .rsp).toNat + 24) % 18446744073709551616 = (s.m.core.read .rsp).toNat - 16 := by
    rw [hu2r]; omega
  have q32 : ((u2.m.core.read .rsp).toNat + 32) % 18446744073709551616 = (s.m.core.read .rsp).toNat - 8 := by
    rw [hu2r]; omega
  have q40 : ((u2.m.core.read .rsp).toNat + 40) % 18446744073709551616 = (s.m.core.read .rsp).toNat := by
    rw [hu2r]; omega
  have sv1 := sv (32, s.m.core.read .rbx) (by simp [sv4])
  have sv2 := sv (24, s.m.core.read .r12) (by simp [sv4])
  have sv3 := sv (16, s.m.core.read .r13) (by simp [sv4])
  have sv5 := sv (8, s.m.core.read .rbp) (by simp [sv4])
  have hretT : t.m.memory.readBytes (s.m.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [Silmaril.X86.FnContract.retOf s.m.core s.m.memory]) := by
    rw [hkU.readBytes (fun j hj => Or.inr (by omega)), (Body.keep hB3).readBytes (fun j hj => Or.inr (by omega))]
    exact habi.returnAddress
  simp only at sv1 sv2 sv3 sv5
  refine must_listed (o := 39) shaC_listing_ok.2.2.1 rfl hdT (by rw [hripT]; exact hin _ (by decide))
    hmT.closeStream (by rw [hripT, ripadd]) ?_
  xstep [hripT]
  refine must_listed (o := 42) shaC_listing_ok.2.2.1 rfl hdT (hin _ (by decide)) hmT.closeStream (by rw [ripadd]) ?_
  xstep [eval_ne_testD, hz12]
  refine must_listed (o := 44) shaC_listing_ok.2.2.1 rfl hdT (hin _ (by decide)) hmT.closeStream (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 46) shaC_listing_ok.2.2.1 rfl hdT (hin _ (by decide)) hmT.closeStream (by rw [ripadd]) ?_
  xstep [eval_e_testD, hzax]
  refine must_listed (o := 69) shaC_listing_ok.2.2.1 rfl hdT (hin _ (by decide)) hmT.closeStream (by rw [ripadd]) ?_
  xstep [hrspT]
  refine must_listed (o := 73) shaC_listing_ok.2.2.1 rfl hdT (hin _ (by decide)) hmT.closeStream (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, q8, sv1]
  refine must_listed (o := 74) shaC_listing_ok.2.2.1 rfl hdT (hin _ (by decide)) hmT.closeStream (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, q16, sv2]
  refine must_listed (o := 76) shaC_listing_ok.2.2.1 rfl hdT (hin _ (by decide)) hmT.closeStream (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, q24, sv3]
  refine must_listed (o := 78) shaC_listing_ok.2.2.1 rfl hdT (hin _ (by decide)) hmT.closeStream (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, q32, sv5]
  refine must_listed (o := 79) shaC_listing_ok.2.2.1 rfl hdT (hin _ (by decide)) hmT.closeStream (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, q40, hretT]
  have hgs : u2.g = s.g := hg3
  refine k _ ⟨rfl, ?_, ?_⟩ ?_ ?_ ?_ ?_ hdT ?_ ?_ ?_ ?_ ?_
  · simp only [st_read_mk, Silmaril.Machine.RegisterFile.write_same]; rw [hB3.rsp]; bv_omega
  · intro r hr
    simp only [Silmaril.X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · simp
    · simp
    · simp [hcsT .r14 (by simp [Silmaril.X86.sysv64_calleeSaved]), hr143]
    · simp [hcsT .r15 (by simp [Silmaril.X86.sysv64_calleeSaved]), hr153]
  · exact (Body.keep hB3).trans (hkU.mono fun x hx => by rcases hx with h | h; exact Or.inl h; exact Or.inr (by omega))
  · rw [hoT]; simp [hgs]
  · rw [hjT]; simp [hgs]
  · rw [haT]; simp [hgs]
  · rw [hiT]; simp [hgs]
  · rw [heT]; simp [hgs]
  · exact hzT
  · intro f' st' hne h
    exact hOT f' st' (by simpa [hrdi3] using hne)
      (by simpa using file_push (v := b + 17895#64) (hO3 f' st' hne h) (by rw [hu28]; omega))
  · intro x h1 h2 acc
    show t.m.memory.permits acc x = _
    rw [← hB3.perm x h1 h2 acc]
    by_cases hx : (s.m.core.read .rsp).toNat - 48 ≤ x
    · rw [(hkT x (Or.inr (by show (u2.m.core.read .rsp - 8#64).toNat ≤ x; rw [hu28]; exact hx))).2 acc]
      simp [pushMem_permits]
    · have e : (u2.m.core.read .rsp - 8#64).toNat = (s.m.core.read .rsp).toNat - 48 := hu28
      rw [hPT x (by show (u2.m.core.read .rsp - 8#64).toNat - 0x80000 ≤ x; rw [e]; exact below_a1 h1)
        (by show x < (u2.m.core.read .rsp - 8#64).toNat + 8; rw [e]; exact below_a2 hx) acc]
      simp [pushMem_permits]

end Silmaril.Elf.Link.Dyn.Sha256sum
