module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.FopenSafer

/-! # GNU `sha256sum`: `fopen_safer` on a file that cannot be opened

`fopen_safer (path, "r")` (`0x4e90`): `fopen` (through gnulib's `rpl_fopen`, `0x4dc0`) returns
`NULL` with `errno` set; `fopen_safer` returns `NULL` (`0x4f26`: `rbx = 0`, the common epilogue
`0x4ec1`). `sha_fopenSaferNull` is `sha_fopenSafer`'s refused-open counterpart: the same prologue
and call, then the `NULL` branch.
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
set_option maxHeartbeats 2000000 in
/-- **`fopen_safer (path, "r")`** (`0x4e90`) on a path the file system refuses with `e`: returns
`NULL` with `errno = e`, keeping the caller's data, the streams, the library state and the
library's non-private memory. -/
theorem sha_fopenSaferNull {E : Env} {W : World} {b lb kb : Word} (I : CloseImps E W b lb)
    (hfo : ImpOk W (lb + 0x85f40#64) (nm "fopen") (fopenStep E W)) {Q : PState → Prop}
    {s : PState} (hrip : s.m.core.rip = b + 0x4e90#64) (habi : AbiEntry s.m.core s.m.memory)
    (hroom : Room W s.m.memory (s.m.core.read .rsp) 256) (hlo : E.S.lo + 256 ≤ (s.m.core.read .rsp).toNat)
    (hd : s.g.done = none) (hm : ShaMemCD b lb kb s.m.memory)
    {p : List Byte} (hp : CStr s.m.memory (s.m.core.read .rdi) p)
    (hpk : ∀ j, j < p.length + 1 → W.Kept ((s.m.core.read .rdi).toNat + j))
    {e : Silmaril.Apps.Sha256sum.Errno} (hfs : E.fs (toSpec p) = .openErr e)
    (k : ∀ t, AbiReturn s.m.core s.m.memory t.m.core →
      Keeps (fun a => W.Kept a ∨ (s.m.core.read .rsp).toNat ≤ a) s.m.memory t.m.memory → t.g = s.g →
      t.m.core.read .rax = 0#64 → ErrnoIs E t.m.memory e →
      (∀ f' st', E.S.file s.m.memory f' st' → E.S.file t.m.memory f' st') →
      t.m.core.fsBase = s.m.core.fsBase → PermKept s t.m.memory →
      Keeps (fun a => ¬ E.S.priv s.m.memory a ∧ s.m.memory.permits .read a = true ∧
        ((s.m.core.read .rsp).toNat ≤ a ∨ a + 256 < (s.m.core.read .rsp).toNat)) s.m.memory t.m.memory →
      (∀ a, E.S.priv t.m.memory a → E.S.priv s.m.memory a ∨ s.m.memory.permits .read a = false) →
      MustQ W Q t) :
    MustQ W Q s := by
  have hin : ∀ n, n < 0xa188 → W.InImage (b + BitVec.ofNat 64 n).toNat := fun n hn => sha_in' I.img I.hb hn
  have hsp := hroom.1
  have hsp2 := hroom.2.1
  have hal := habi.aligned
  have e8 : (s.m.core.read .rsp - 8#64).toNat = (s.m.core.read .rsp).toNat - 8 :=
    sub_toNat (k := 8) (by omega) (by decide)
  have e16 : (s.m.core.read .rsp - 8#64 - 8#64).toNat = (s.m.core.read .rsp).toNat - 16 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), e8]; omega
  have e24 : (s.m.core.read .rsp - 8#64 - 8#64 - 8#64).toNat = (s.m.core.read .rsp).toNat - 24 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), e16]; omega
  have e32 : (s.m.core.read .rsp - 8#64 - 8#64 - 8#64 - 8#64).toNat = (s.m.core.read .rsp).toNat - 32 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), e24]; omega
  have p1 : s.m.memory.Permitted .write (s.m.core.read .rsp - 8#64).toNat 8 :=
    room_perm hroom (Or.inr rfl) (by omega) (by omega)
  have p2 : s.m.memory.Permitted .write (s.m.core.read .rsp - 8#64 - 8#64).toNat 8 :=
    room_perm hroom (Or.inr rfl) (by omega) (by omega)
  have p3 : s.m.memory.Permitted .write (s.m.core.read .rsp - 8#64 - 8#64 - 8#64).toNat 8 :=
    room_perm hroom (Or.inr rfl) (by omega) (by omega)
  have p4 : s.m.memory.Permitted .write (s.m.core.read .rsp - 8#64 - 8#64 - 8#64 - 8#64).toNat 8 :=
    room_perm hroom (Or.inr rfl) (by omega) (by omega)
  have r1 : s.m.memory.Permitted .read (s.m.core.read .rsp - 8#64).toNat 8 :=
    room_perm hroom (Or.inl rfl) (by omega) (by omega)
  have r2 : s.m.memory.Permitted .read (s.m.core.read .rsp - 8#64 - 8#64).toNat 8 :=
    room_perm hroom (Or.inl rfl) (by omega) (by omega)
  have r3 : s.m.memory.Permitted .read (s.m.core.read .rsp - 8#64 - 8#64 - 8#64).toNat 8 :=
    room_perm hroom (Or.inl rfl) (by omega) (by omega)
  have r4 : s.m.memory.Permitted .read (s.m.core.read .rsp - 8#64 - 8#64 - 8#64 - 8#64).toNat 8 :=
    room_perm hroom (Or.inl rfl) (by omega) (by omega)
  have hMk := shaMemCD_keep (lb := lb) (kb := kb) I.img I.hb
  have hm1 := hMk _ _ hm (room_push_img (v := s.m.core.read .rbp) (sp' := s.m.core.read .rsp) hroom (by omega) (by omega))
  have hm2 := hMk _ _ hm1 (room_push_img (v := s.m.core.read .r13) (sp' := s.m.core.read .rsp - 8#64) hroom
    (by rw [e8]; omega) (by rw [e8]; omega))
  have hm3 := hMk _ _ hm2 (room_push_img (v := s.m.core.read .r12) (sp' := s.m.core.read .rsp - 8#64 - 8#64) hroom
    (by rw [e16]; omega) (by rw [e16]; omega))
  have hm4 := hMk _ _ hm3 (room_push_img (v := s.m.core.read .rbx) (sp' := s.m.core.read .rsp - 8#64 - 8#64 - 8#64)
    hroom (by rw [e24]; omega) (by rw [e24]; omega))
  refine must_listed (o := 0) shaD_listing_ok.2.1 rfl hd (by rw [hrip]; exact hin _ (by decide)) hm.2.fopenSafer
    (by rw [hrip]; exact (BitVec.add_zero _).symm) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa using p1)]
  xstep [hrip]
  refine must_listed (o := 1) shaD_listing_ok.2.1 rfl hd (hin _ (by decide)) hm1.2.fopenSafer (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 4) shaD_listing_ok.2.1 rfl hd (hin _ (by decide)) hm1.2.fopenSafer (by rw [ripadd]) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa [pushMem_permitted] using p2)]
  xstep []
  refine must_listed (o := 6) shaD_listing_ok.2.1 rfl hd (hin _ (by decide)) hm2.2.fopenSafer (by rw [ripadd]) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa [pushMem_permitted] using p3)]
  xstep []
  refine must_listed (o := 8) shaD_listing_ok.2.1 rfl hd (hin _ (by decide)) hm3.2.fopenSafer (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 15) shaD_listing_ok.2.1 rfl hd (hin _ (by decide)) hm3.2.fopenSafer (by rw [ripadd]) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa [pushMem_permitted] using p4)]
  xstep []
  refine must_listed (o := 16) shaD_listing_ok.2.1 rfl hd (hin _ (by decide)) hm4.2.fopenSafer (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 19) shaD_listing_ok.2.1 rfl hd (hin _ (by decide)) hm4.2.fopenSafer (by rw [ripadd]) ?_
  xstep []
  have hkc : Keeps (fun a => W.Kept a ∨ (s.m.core.read .rsp).toNat ≤ a) s.m.memory
      (pushMem (pushMem (pushMem (pushMem s.m.memory (s.m.core.read .rsp) (s.m.core.read .rbp))
        (s.m.core.read .rsp - 8#64) (s.m.core.read .r13)) (s.m.core.read .rsp - 8#64 - 8#64) (s.m.core.read .r12))
        (s.m.core.read .rsp - 8#64 - 8#64 - 8#64) (s.m.core.read .rbx)) :=
    ((((room_push_caller hroom (by omega) (by omega)).trans
      (room_push_caller hroom (by rw [e8]; omega) (by rw [e8]; omega))).trans
      (room_push_caller hroom (by rw [e16]; omega) (by rw [e16]; omega))).trans
      (room_push_caller hroom (by rw [e24]; omega) (by rw [e24]; omega)))
  refine must_gen (fun u => Body W (ShaMemCD b lb kb) s u 40 256 (sv4 s) ∧ u.m.core.rip = b + 0x4ea7#64 ∧
      u.m.core.read .rdi = s.m.core.read .rdi ∧ u.m.core.read .rbp = s.m.core.read .rsp - 8#64 ∧
      u.m.core.read .r14 = s.m.core.read .r14 ∧ u.m.core.read .r15 = s.m.core.read .r15 ∧ u.g = s.g ∧
      CStr u.m.memory (s.m.core.read .rdi) p ∧
      (∀ f st, E.S.file s.m.memory f st → E.S.file u.m.memory f st) ∧
      Keeps (fun a => (s.m.core.read .rsp).toNat ≤ a ∨ a + 40 < (s.m.core.read .rsp).toNat) s.m.memory u.m.memory ∧
      (∀ acc a, u.m.memory.permits acc a = s.m.memory.permits acc a)) ?_ ?_
  · refine ⟨⟨?_, keepF hkc, hroom.pushMem.pushMem.pushMem.pushMem, hm4, rfl, hd, ?_,
      fun a _ _ acc => by simp [pushMem_permits]⟩, rfl, by simp, by simp, by simp, by simp, rfl, ?_, ?_, ?_, ?_⟩
    · simp; bv_omega
    · intro q hq
      simp only [sv4, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · simp only
        rw [read_push_ne (by rw [e32, e24]; omega) (by rw [e24]; omega) (by rw [e24]; omega),
          read_push_ne (by rw [e24, e16]; omega) (by rw [e16]; omega) (by rw [e16]; omega),
          read_push_ne (by rw [e16, e8]; omega) (by rw [e8]; omega) (by rw [e8]; omega)]
        exact push_read_at r1 p1 e8
      · simp only
        rw [read_push_ne (by rw [e32, e24]; omega) (by rw [e24]; omega) (by rw [e24]; omega),
          read_push_ne (by rw [e24, e16]; omega) (by rw [e16]; omega) (by rw [e16]; omega),
          show (s.m.core.read .rsp).toNat - 16 = (s.m.core.read .rsp - 8#64).toNat - 8 by rw [e8]; omega]
        exact push_read_at (by simpa [pushMem_permitted] using r2) (by simpa [pushMem_permitted] using p2)
          (by rw [e16, e8]; omega)
      · simp only
        rw [read_push_ne (by rw [e32, e24]; omega) (by rw [e24]; omega) (by rw [e24]; omega),
          show (s.m.core.read .rsp).toNat - 24 = (s.m.core.read .rsp - 8#64 - 8#64).toNat - 8 by rw [e16]; omega]
        exact push_read_at (by simpa [pushMem_permitted] using r3) (by simpa [pushMem_permitted] using p3)
          (by rw [e24, e16]; omega)
      · simp only
        rw [show (s.m.core.read .rsp).toNat - 32 = (s.m.core.read .rsp - 8#64 - 8#64 - 8#64).toNat - 8 by rw [e24]; omega]
        exact push_read_at (by simpa [pushMem_permitted] using r4) (by simpa [pushMem_permitted] using p4)
          (by rw [e32, e24]; omega)
    · refine ⟨hp.1, ?_⟩
      rw [(hkc.mono fun x hx => Or.inl hx).readBytes (fun j hj => hpk j hj)]
      exact hp.2
    · intro f st h
      exact file_push (file_push (file_push (file_push h (by rw [e8]; omega)) (by rw [e16]; omega))
        (by rw [e24]; omega)) (by rw [e32]; omega)
    · exact (((pushMem_keeps fun x hx => by rw [e8]; omega).trans (pushMem_keeps fun x hx => by rw [e16]; omega)).trans
        (pushMem_keeps fun x hx => by rw [e24]; omega)).trans (pushMem_keeps fun x hx => by rw [e32]; omega)
    · intro acc a; simp [pushMem_permits]
  rintro u ⟨hB, hrip1, hrdi1, hrbp1, hr141, hr151, hg1, hp1, hfk1, hkU, hpU⟩
  have hur : (u.m.core.read .rsp).toNat = (s.m.core.read .rsp).toNat - 40 := by
    rw [hB.rsp]; exact sub_toNat (by omega) (by decide)
  have hu8 : (u.m.core.read .rsp - 8#64).toNat = (s.m.core.read .rsp).toNat - 48 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), hur]; omega
  have pw : u.m.memory.Permitted .write (u.m.core.read .rsp - 8#64).toNat 8 :=
    room_perm hB.room (Or.inr rfl) (by omega) (by omega)
  have pr : u.m.memory.Permitted .read (u.m.core.read .rsp - 8#64).toNat 8 :=
    room_perm hB.room (Or.inl rfl) (by omega) (by omega)
  have hmp := hMk _ _ hB.mem (room_push_img (v := b + 20140#64) (sp' := u.m.core.read .rsp) hB.room
    (by rw [hur]; omega) (by rw [hur]; omega))
  have hkp : Keeps W.Kept u.m.memory (pushMem u.m.memory (u.m.core.read .rsp) (b + 20140#64)) :=
    (room_push_caller hB.room (by rw [hur]; omega) (by rw [hur]; omega)).mono fun x hx => Or.inl hx
  have hpp : CStr (pushMem u.m.memory (u.m.core.read .rsp) (b + 20140#64)) (s.m.core.read .rdi) p :=
    ⟨hp1.1, by rw [hkp.readBytes (fun j hj => hpk j hj)]; exact hp1.2⟩
  refine must_listed (o := 23) shaD_listing_ok.2.1 rfl hB.done (by rw [hrip1]; exact hin _ (by decide))
    hB.mem.2.fopenSafer (by rw [hrip1, ripadd]) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa using pw)]
  xstep [hrip1]
  refine must_listed (o := 0) shaD_listing_ok.1 rfl hB.done (hin _ (by decide)) hmp.2.fopenR (by simp) ?_
  xstep []
  refine must_plt_jmp (o := 7) (so := 0x1f0) (pb := b + 0x23c0#64) hB.done I.lz shaD_listing_ok.1 rfl
    (hin _ (by decide)) hmp.2.fopenR (by rw [ripadd]) shaC_listing_ok.1 rfl rfl
    (by simp only [BitVec.add_assoc]; rfl)
    (img_off I.img I.hb (by decide)) (img_off I.img I.hb (by decide)) hmp.1.plt
    (by
      rw [show b + 0x23c0#64 + BitVec.ofNat 64 (0x1f0 + 4 + 6) + BitVec.signExtend 64 0x7916#32 = b + 0x9ed0#64 by
        simp only [BitVec.add_assoc]; rfl]
      exact hmp.2.fopen)
    hfo.1 hfo.2.1 hfo.2.2.1 (fun r h => (impOk_fn hfo _ r).1 h)
    ⟨abiEntry_of (v := b + 20140#64) (by show (u.m.core.read .rsp - 8#64).toNat % 16 = 8; rw [hu8]; omega)
        (by simpa [jmpEntry] using pushMem_read pr pw),
      ⟨p, by simpa [jmpEntry, hrdi1] using hpp⟩, ⟨by decide, by simpa [jmpEntry] using hmp.2.rstr⟩⟩ ?_
  intro v hv
  obtain ⟨⟨hret, hfsv, hspv, hnpv, hprv, -⟩, hgv, hokv, hopen⟩ := hv
  have hop := hopen p (by simpa [jmpEntry, hrdi1] using hpp)
  rw [hfs] at hop
  obtain ⟨hnull, hfiles, herr⟩ := hop
  have hsv4 : ∀ q ∈ sv4 s, q.1 ≤ 32 ∧ 32 ≤ 40 := by
    intro q hq
    simp only [sv4, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> simp
  obtain ⟨hB2, hrip2, hrsp2, hcs2⟩ := body_after (shaMemCD_keep I.img I.hb) hB (by decide) (by decide) hsv4
    (ret := b + 20140#64) (hpost := ⟨hret, halfOfStack hspv, by rw [hgv]; exact hB.done⟩) (hem := by exact rfl)
    (hersp := by simp [jmpEntry]) (hecs := by
      intro r hr
      simp only [Silmaril.X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [jmpEntry])
    (hefs := by exact rfl) (hvfs := hfsv) (hfp := fun x h => absurd hnull h.1) (hX := fun x h => h.elim)
  have herrv : ErrnoIs E v.m.memory e := herr e rfl
  have hO2 : ∀ f st, E.S.file s.m.memory f st → E.S.file v.m.memory f st := fun f st h =>
    hokv f st (by simp) (by simpa [jmpEntry] using file_push (v := b + 20140#64) (hfk1 f st h) (by rw [hu8]; omega))
  refine must_listed (o := 28) shaD_listing_ok.2.1 rfl hB2.done (by rw [hrip2]; exact hin _ (by decide))
    hB2.mem.2.fopenSafer (by rw [hrip2, ripadd]) ?_
  xstep [hrip2]
  refine must_listed (o := 31) shaD_listing_ok.2.1 rfl hB2.done (hin _ (by decide)) hB2.mem.2.fopenSafer (by rw [ripadd]) ?_
  xstep [eval_e_testQ, hnull]
  refine must_listed (o := 150) shaD_listing_ok.2.1 rfl hB2.done (hin _ (by decide)) hB2.mem.2.fopenSafer
    (by simp only [ripadd]) ?_
  xstep []
  refine must_listed (o := 152) shaD_listing_ok.2.1 rfl hB2.done (hin _ (by decide)) hB2.mem.2.fopenSafer (by rw [ripadd]) ?_
  xstep []
  have hvr : (v.m.core.read .rsp).toNat = (s.m.core.read .rsp).toNat - 40 := by
    rw [hB2.rsp]; exact sub_toNat (by omega) (by decide)
  have q8 : ((v.m.core.read .rsp).toNat + 8) % 18446744073709551616 = (s.m.core.read .rsp).toNat - 32 := by
    rw [hvr]; omega
  have q16 : ((v.m.core.read .rsp).toNat + 16) % 18446744073709551616 = (s.m.core.read .rsp).toNat - 24 := by
    rw [hvr]; omega
  have q24 : ((v.m.core.read .rsp).toNat + 24) % 18446744073709551616 = (s.m.core.read .rsp).toNat - 16 := by
    rw [hvr]; omega
  have q32 : ((v.m.core.read .rsp).toNat + 32) % 18446744073709551616 = (s.m.core.read .rsp).toNat - 8 := by
    rw [hvr]; omega
  have q40 : ((v.m.core.read .rsp).toNat + 40) % 18446744073709551616 = (s.m.core.read .rsp).toNat := by
    rw [hvr]; omega
  have sv1 := hB2.saved (32, s.m.core.read .rbx) (by simp [sv4])
  have sv2 := hB2.saved (24, s.m.core.read .r12) (by simp [sv4])
  have sv3 := hB2.saved (16, s.m.core.read .r13) (by simp [sv4])
  have sv5 := hB2.saved (8, s.m.core.read .rbp) (by simp [sv4])
  simp only at sv1 sv2 sv3 sv5
  have hretv : v.m.memory.readBytes (s.m.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [Silmaril.X86.FnContract.retOf s.m.core s.m.memory]) := by
    rw [(Body.keep hB2).readBytes (fun j hj => Or.inr (by omega))]; exact habi.returnAddress
  refine must_listed (o := 49) shaD_listing_ok.2.1 rfl hB2.done (hin _ (by decide)) hB2.mem.2.fopenSafer
    (by simp only [ripadd]) ?_
  xstep []
  refine must_listed (o := 53) shaD_listing_ok.2.1 rfl hB2.done (hin _ (by decide)) hB2.mem.2.fopenSafer (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 56) shaD_listing_ok.2.1 rfl hB2.done (hin _ (by decide)) hB2.mem.2.fopenSafer (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, q8, sv1]
  refine must_listed (o := 57) shaD_listing_ok.2.1 rfl hB2.done (hin _ (by decide)) hB2.mem.2.fopenSafer (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, q16, sv2]
  refine must_listed (o := 59) shaD_listing_ok.2.1 rfl hB2.done (hin _ (by decide)) hB2.mem.2.fopenSafer (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, q24, sv3]
  refine must_listed (o := 61) shaD_listing_ok.2.1 rfl hB2.done (hin _ (by decide)) hB2.mem.2.fopenSafer (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, q32, sv5]
  refine must_listed (o := 62) shaD_listing_ok.2.1 rfl hB2.done (hin _ (by decide)) hB2.mem.2.fopenSafer (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, q40, hretv]
  have hgv' : v.g = s.g := by rw [hgv]; simp [jmpEntry, hg1, hfiles]
  refine k _ ⟨rfl, ?_, ?_⟩ (Body.keep (u := v) hB2) hgv' (by simp [Silmaril.X86.Ext.AluOp.resultN]) herrv hO2 hB2.fs hB2.perm ?_ ?_
  · simp only [st_read_mk, Silmaril.Machine.RegisterFile.write_same]; rw [hB2.rsp]; bv_omega
  · intro r hr
    have hr' := hr
    simp only [Silmaril.X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · simp
    · simp
    · simp only [st_read_mk, Silmaril.Machine.RegisterFile.write_other, ne_eq, reduceCtorEq, not_false_eq_true]
      rw [st_regs_apply, hcs2 _ hr, hr141]
    · simp only [st_read_mk, Silmaril.Machine.RegisterFile.write_other, ne_eq, reduceCtorEq, not_false_eq_true]
      rw [st_regs_apply, hcs2 _ hr, hr151]
  · -- the library's non-private memory outside the frame
    have hk1 : Keeps (fun a => (s.m.core.read .rsp).toNat ≤ a ∨ a + 256 < (s.m.core.read .rsp).toNat) s.m.memory
        (pushMem u.m.memory (u.m.core.read .rsp) (b + 20140#64)) :=
      (hkU.mono fun a ha => by omega).trans (pushMem_keeps fun x hx => by rw [hu8]; omega)
    have hpr1 : E.S.priv (pushMem u.m.memory (u.m.core.read .rsp) (b + 20140#64)) = E.S.priv s.m.memory :=
      E.S.priv_keep _ _ (hk1.mono fun a ha => Or.inr (by have := E.S.priv_lo _ _ ha; omega))
    intro a ⟨hnp, hrd, hout⟩
    have h1 := hk1 a hout
    have h2 := hnpv a ⟨by simp only [jmpEntry]; rw [hpr1]; exact hnp, fun h => absurd hnull h.1,
      by simp only [jmpEntry]; rw [h1.2]; exact hrd⟩
    simp only [jmpEntry] at h2
    exact ⟨h2.1.trans h1.1, fun acc => (h2.2 acc).trans (h1.2 acc)⟩
  · intro a ha
    have hpr1 : E.S.priv (pushMem u.m.memory (u.m.core.read .rsp) (b + 20140#64)) = E.S.priv s.m.memory :=
      E.S.priv_keep _ _ ((hkU.mono fun a ha => Or.inr (by have := E.S.priv_lo _ _ ha; omega)).trans
        (pushMem_keeps fun x hx => by rw [hu8]; have := E.S.priv_lo _ _ hx; omega))
    rcases hprv a ha with h | h
    · simp only [jmpEntry] at h; rw [hpr1] at h; exact Or.inl h
    · simp only [jmpEntry, pushMem_permits] at h; rw [hpU] at h; exact Or.inr h

end Silmaril.Elf.Link.Dyn.Sha256sum
