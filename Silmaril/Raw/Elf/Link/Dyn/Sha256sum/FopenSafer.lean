module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.CloseIn
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MemDigest

/-! # GNU `sha256sum`: `fopen_safer` on a readable file -/

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

/-- `cmp r32, imm` as the semantics builds it. -/
abbrev cmpD (x y : BitVec 32) : Silmaril.X86.Flags :=
  @Silmaril.X86.Ext.AluOp.flagsN Silmaril.X86.Ext.Sz.d.bits Silmaril.X86.AluOp.cmp x y

theorem eval_cmpD (x y : BitVec 32) (c : Silmaril.X86.Ext.Cond) :
    Silmaril.X86.Ext.Cond.eval (cmpD x y) c = some (Silmaril.X86.Ext.Cond.afterCmp (w := 31) x y c) :=
  Silmaril.X86.Ext.eval_subFlagsN (w := 31) x y c

/-- `test r64, r64` as the semantics builds it. -/
abbrev andQ (x y : BitVec 64) : BitVec 64 :=
  @HAnd.hAnd (BitVec 64) (BitVec 64) (BitVec 64)
    (@instHAndOfAndOp (BitVec Silmaril.X86.Ext.Sz.q.bits) (@BitVec.instAndOp Silmaril.X86.Ext.Sz.q.bits)) x y

theorem eval_e_testQ (x : BitVec 64) :
    Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.logicFlagsN (andQ x x)) .e = some (decide (x = 0#64)) :=
  Silmaril.X86.BlockCert9.eval_e_test x
theorem eval_ne_testQ (x : BitVec 64) :
    Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.logicFlagsN (andQ x x)) .ne = some (!decide (x = 0#64)) :=
  eval_ne_test x

theorem shaMemD_keep {b lb kb : Word} {W : World} (I : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64) :
    ∀ m m', ShaMemD b lb kb m → Keeps W.InImage m m' → ShaMemD b lb kb m' :=
  fun _ _ hm h => hm.keep hb (by rw [I] at h; exact h)

/-- Both image facts. -/
def ShaMemCD (b lb kb : Word) (m : Memory) : Prop := ShaMemC b lb m ∧ ShaMemD b lb kb m

theorem shaMemCD_keep {b lb kb : Word} {W : World} (I : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64) :
    ∀ m m', ShaMemCD b lb kb m → Keeps W.InImage m m' → ShaMemCD b lb kb m' :=
  fun m m' hm h => ⟨shaMemC_keep I hb m m' hm.1 h, shaMemD_keep I hb m m' hm.2 h⟩

/-- The library state after `fopen` opened a stream. -/
def _root_.Silmaril.Elf.Link.Dyn.Proc.Ghost.opened (g : Ghost) : Ghost := { g with files := g.files + 1 }

/-- The library state after `malloc` served `n` bytes. -/
def _root_.Silmaril.Elf.Link.Dyn.Proc.Ghost.alloc (g : Ghost) (n : Nat) : Ghost :=
  { g with allocs := g.allocs + 1, heap := g.heap + n }

/-- The library state with the live block `(p, n)` added (between `malloc` and `free`). -/
def _root_.Silmaril.Elf.Link.Dyn.Proc.Ghost.withBlk (g : Ghost) (p n : Nat) : Ghost :=
  { g with blocks := (p, n) :: g.blocks }

@[simp] theorem withBlk_erase (g : Ghost) (p n : Nat) :
    { g.withBlk p n with blocks := (g.withBlk p n).blocks.eraseP (·.1 == p) } = g := by
  simp [Proc.Ghost.withBlk]

@[simp] theorem withBlk_at (g : Ghost) (p n : Nat) : blockAt (g.withBlk p n) p = some n := by
  simp [Proc.Ghost.withBlk, blockAt]

/-- The stream `fopen` opens on a readable file. -/
def openSt (data : Silmaril.Apps.Sha256sum.Bytes) (fd : Nat) : St := ⟨fd, true, ofSpec data, false, false, false, []⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- **`fopen_safer (path, "r")`** (`0x4e90`) on a readable file: returns the new stream (its
descriptor is above 2, so gnulib does not move it). -/
theorem sha_fopenSafer {E : Env} {W : World} {b lb kb : Word} (I : CloseImps E W b lb)
    (hfo : ImpOk W (lb + 0x85f40#64) (nm "fopen") (fopenStep E W)) {Q : PState → Prop}
    {s : PState} (hrip : s.m.core.rip = b + 0x4e90#64) (habi : AbiEntry s.m.core s.m.memory)
    (hroom : Room W s.m.memory (s.m.core.read .rsp) 256) (hlo : E.S.lo + 256 ≤ (s.m.core.read .rsp).toNat)
    (hd : s.g.done = none) (hm : ShaMemCD b lb kb s.m.memory)
    {p : List Byte} (hp : CStr s.m.memory (s.m.core.read .rdi) p)
    (hpk : ∀ j, j < p.length + 1 → W.Kept ((s.m.core.read .rdi).toNat + j))
    {data : Silmaril.Apps.Sha256sum.Bytes} (hfs : E.fs (toSpec p) = .ok data) (hres : E.allocOk = true)
    (hroomF : InMain s.g ∧ s.g.files < E.maxOpen ∧ data.length ≤ E.maxFile)
    (k : ∀ t (fd : Nat), AbiReturn s.m.core s.m.memory t.m.core →
      Keeps (fun a => W.Kept a ∨ (s.m.core.read .rsp).toNat ≤ a) s.m.memory t.m.memory → t.g = s.g.opened →
      E.S.file t.m.memory (t.m.core.read .rax) (openSt data fd) → 3 ≤ fd → fd < 2 ^ 31 →
      t.m.core.read .rax ≠ 0#64 → (∀ st0, ¬ E.S.file s.m.memory (t.m.core.read .rax) st0) →
      (∀ f' st', E.S.file s.m.memory f' st' → E.S.file t.m.memory f' st') →
      t.m.core.fsBase = s.m.core.fsBase → PermKept s t.m.memory → LibK E W s.m.memory t.m.memory → MustQ W Q t) :
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
      (∀ f st, E.S.file s.m.memory f st → E.S.file u.m.memory f st) ∧ LibK E W s.m.memory u.m.memory) ?_ ?_
  · refine ⟨⟨?_, keepF hkc, hroom.pushMem.pushMem.pushMem.pushMem, hm4, rfl, hd, ?_,
      fun a _ _ acc => by simp [pushMem_permits]⟩, rfl, by simp, by simp, by simp, by simp, rfl, ?_, ?_,
      ((((LibK.refl E W _).push (by rw [e8]; omega)).push (by rw [e16]; omega)).push (by rw [e24]; omega)).push
        (by rw [e32]; omega)⟩
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
  rintro u ⟨hB, hrip1, hrdi1, hrbp1, hr141, hr151, hg1, hp1, hfk1, hLu⟩
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
  obtain ⟨hLR, hgv, hokv, hopen⟩ := hv
  obtain ⟨hret, hfsv, hspv, -, -⟩ := id hLR
  have hop := hopen p (by simpa [jmpEntry, hrdi1] using hpp)
  rw [hfs] at hop
  rcases hop with ⟨-, hno, -⟩ | ⟨fd, hfv, hnz, hfd3, hfd31, hfiles, hfoot, hnew⟩
  · exfalso
    rcases hno with hno | hno
    · rw [hres] at hno; cases hno
    · apply hno
      refine ⟨by simp only [jmpEntry]; rw [hg1]; exact hroomF.1, ?_, by simp only [jmpEntry]; rw [hg1]; exact hroomF.2.1,
        by simp [ofSpec]; exact hroomF.2.2⟩
      simp only [jmpEntry, st_read_mk, Silmaril.Machine.RegisterFile.write_other, ne_eq, reduceCtorEq,
        not_false_eq_true, Silmaril.Machine.RegisterFile.write_same]
      rw [hu8]; omega
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
    (hefs := by exact rfl) (hvfs := hfsv) (hfp := fun x h => by
      have hf := hfoot x h.2
      refine ⟨hf.1, Or.inl ?_⟩
      have := hf.2.1
      simp only [jmpEntry, st_read_mk, Silmaril.Machine.RegisterFile.write_other, ne_eq, reduceCtorEq,
        not_false_eq_true, Silmaril.Machine.RegisterFile.write_same] at this
      rw [hu8] at this; omega) (hX := fun x h => h.elim)
  have hfv' : E.S.file v.m.memory (v.m.core.read .rax) (openSt data fd) := hfv
  have hLj : LibK E W s.m.memory (pushMem u.m.memory (u.m.core.read .rsp) (b + 20140#64)) :=
    hLu.push (by rw [hu8]; omega)
  have hLv : LibK E W s.m.memory v.m.memory :=
    LibK.libRet (by exact hLj) hLR fun a ha hf => hLj.fresh (hfoot a hf.2).2.2 ha
  have hO2 : ∀ f st, E.S.file s.m.memory f st → E.S.file v.m.memory f st := fun f st h =>
    hokv f st (by simp) (by simpa [jmpEntry] using file_push (v := b + 20140#64) (hfk1 f st h) (by rw [hu8]; omega))
  refine must_listed (o := 28) shaD_listing_ok.2.1 rfl hB2.done (by rw [hrip2]; exact hin _ (by decide))
    hB2.mem.2.fopenSafer (by rw [hrip2, ripadd]) ?_
  xstep [hrip2]
  refine must_listed (o := 31) shaD_listing_ok.2.1 rfl hB2.done (hin _ (by decide)) hB2.mem.2.fopenSafer (by rw [ripadd]) ?_
  xstep [eval_e_testQ, hnz]
  refine must_listed (o := 33) shaD_listing_ok.2.1 rfl hB2.done (hin _ (by decide)) hB2.mem.2.fopenSafer (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 36) shaD_listing_ok.2.1 rfl hB2.done (hin _ (by decide)) hB2.mem.2.fopenSafer (by rw [ripadd]) ?_
  xstep []
  refine must_gen (fun u => Body W (ShaMemCD b lb kb) s u 40 256 (sv4 s) ∧ u.m.core.rip = b + 20151#64 ∧
      u.m.core.read .rdi = v.m.core.read .rax ∧ u.m.core.read .rbx = v.m.core.read .rax ∧
      u.m.core.read .rsp = v.m.core.read .rsp ∧ u.g = v.g ∧ u.m.memory = v.m.memory ∧
      u.m.core.read .r14 = s.m.core.read .r14 ∧ u.m.core.read .r15 = s.m.core.read .r15) ?_ ?_
  · exact ⟨hB2.of_eq rfl (by simp) rfl rfl, rfl, by simp, by simp, by simp, rfl, rfl,
      by simp [hcs2 .r14 (by simp [Silmaril.X86.sysv64_calleeSaved]), hr141],
      by simp [hcs2 .r15 (by simp [Silmaril.X86.sysv64_calleeSaved]), hr151]⟩
  rintro w ⟨hB3, hrip3, hrdi3, hrbx3, hrsp3, hg3, hmem3, h14_3, h15_3⟩
  have hw8 : (w.m.core.read .rsp - 8#64).toNat = (s.m.core.read .rsp).toNat - 48 := by
    rw [hrsp3, hrsp2]; exact hu8
  have hfw : E.S.file w.m.memory (v.m.core.read .rax) (openSt data fd) := by rw [hmem3]; exact hfv'
  have hsvq : ∀ q ∈ sv4 s, q.1 ≤ 32 ∧ 32 ≤ 40 := hsv4
  refine body_call (shaMemCD_keep I.img I.hb) hB3 (by decide) (by decide) hsvq (by omega) I.lz
    (o := 39) (so := 0x180) (pb := b + 0x23c0#64) (fp := fun _ => False)
    shaD_listing_ok.2.1 rfl (by rw [hrip3]; exact hin _ (by decide)) (fun m h => h.2.fopenSafer)
    (by rw [hrip3, ripadd]) shaC_listing_ok.1 rfl rfl (by simp only [BitVec.add_assoc]; rfl)
    (img_off I.img I.hb (by decide)) (img_off I.img I.hb (by decide)) (fun m h => h.1.plt)
    (fun m h => by
      rw [show b + 0x23c0#64 + BitVec.ofNat 64 (0x180 + 4 + 6) + BitVec.signExtend 64 0x794e#32 = b + 0x9e98#64 by
        simp only [BitVec.add_assoc]; rfl]
      exact h.1.fileno)
    I.fileno.1 I.fileno.2.1 I.fileno.2.2.1 (fun r h => (impOk_fn I.fileno _ r).1 h)
    (fun he => ⟨he, _, by
      rw [callEntry_mem, callEntry_read _ _ _ (by decide), hrdi3]
      exact file_push hfw (by rw [hw8]; omega)⟩)
    (fun x hx => ⟨hx.1.1, hx.1.2.2.1, by simpa [callEntry] using hx.1.2.1, by rw [hx.2.1]; exact hB3.done⟩)
    (fun x h => h.elim) (fun x h => h.elim) ?_
  intro x hx hB4 hrip4 hrsp4 hcs4
  obtain ⟨hLRx, hgx, hokx, hfdx⟩ := hx
  have hLx : LibK E W s.m.memory x.m.memory := (hLv.of_eq hmem3).call0 (by rw [hw8]; omega) hLRx
  have hfE := file_push (v := b + 20112#64 + BitVec.ofNat 64 (39 + 5)) hfw (by rw [hw8]; omega)
  have hfd32 : BitVec.setWidth 32 (x.m.core.read .rax) = BitVec.ofNat 32 fd :=
    hfdx (openSt data fd) (by rw [callEntry_mem, callEntry_read _ _ _ (by decide), hrdi3]; exact hfE)
  have hfx : E.S.file x.m.memory (v.m.core.read .rax) (openSt data fd) :=
    hokx _ _ (by simp) (by rw [callEntry_mem]; exact hfE)
  have hbe : Silmaril.X86.Ext.Cond.eval (cmpD (BitVec.ofNat 32 fd) 2#32) .be = some false := by
    rw [eval_cmpD]
    simp only [Silmaril.X86.Ext.Cond.afterCmp, BitVec.ule, BitVec.toNat_ofNat, Option.some.injEq]
    rw [Nat.mod_eq_of_lt (show fd < 2 ^ 32 by omega)]
    simp only [decide_eq_false_iff_not]; omega
  have hxr : (x.m.core.read .rsp).toNat = (s.m.core.read .rsp).toNat - 40 := by
    rw [hB4.rsp]; exact sub_toNat (by omega) (by decide)
  have q8 : ((x.m.core.read .rsp).toNat + 8) % 18446744073709551616 = (s.m.core.read .rsp).toNat - 32 := by
    rw [hxr]; omega
  have q16 : ((x.m.core.read .rsp).toNat + 16) % 18446744073709551616 = (s.m.core.read .rsp).toNat - 24 := by
    rw [hxr]; omega
  have q24 : ((x.m.core.read .rsp).toNat + 24) % 18446744073709551616 = (s.m.core.read .rsp).toNat - 16 := by
    rw [hxr]; omega
  have q32 : ((x.m.core.read .rsp).toNat + 32) % 18446744073709551616 = (s.m.core.read .rsp).toNat - 8 := by
    rw [hxr]; omega
  have q40 : ((x.m.core.read .rsp).toNat + 40) % 18446744073709551616 = (s.m.core.read .rsp).toNat := by
    rw [hxr]; omega
  have sv1 := hB4.saved (32, s.m.core.read .rbx) (by simp [sv4])
  have sv2 := hB4.saved (24, s.m.core.read .r12) (by simp [sv4])
  have sv3 := hB4.saved (16, s.m.core.read .r13) (by simp [sv4])
  have sv5 := hB4.saved (8, s.m.core.read .rbp) (by simp [sv4])
  simp only at sv1 sv2 sv3 sv5
  have hretx : x.m.memory.readBytes (s.m.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [Silmaril.X86.FnContract.retOf s.m.core s.m.memory]) := by
    rw [(Body.keep hB4).readBytes (fun j hj => Or.inr (by omega))]; exact habi.returnAddress
  have hrbx4 : x.m.core.read .rbx = v.m.core.read .rax := by
    rw [hcs4 .rbx (by simp [Silmaril.X86.sysv64_calleeSaved]), hrbx3]
  refine must_listed (o := 44) shaD_listing_ok.2.1 rfl hB4.done (by rw [hrip4]; exact img_off I.img I.hb (by decide))
    hB4.mem.2.fopenSafer (by rw [hrip4]) ?_
  xstep [hrip4]
  refine must_listed (o := 47) shaD_listing_ok.2.1 rfl hB4.done (hin _ (by decide)) hB4.mem.2.fopenSafer (by rw [ripadd]) ?_
  have hbe' : Silmaril.X86.Ext.Cond.eval (@Silmaril.X86.Ext.AluOp.flagsN 32 Silmaril.X86.AluOp.cmp
      (BitVec.ofNat 32 fd) 2#32) .be = some false := hbe
  xstep [hfd32, hbe, hbe']
  refine must_listed (o := 49) shaD_listing_ok.2.1 rfl hB4.done (hin _ (by decide)) hB4.mem.2.fopenSafer (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 53) shaD_listing_ok.2.1 rfl hB4.done (hin _ (by decide)) hB4.mem.2.fopenSafer (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 56) shaD_listing_ok.2.1 rfl hB4.done (hin _ (by decide)) hB4.mem.2.fopenSafer (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, q8, sv1]
  refine must_listed (o := 57) shaD_listing_ok.2.1 rfl hB4.done (hin _ (by decide)) hB4.mem.2.fopenSafer (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, q16, sv2]
  refine must_listed (o := 59) shaD_listing_ok.2.1 rfl hB4.done (hin _ (by decide)) hB4.mem.2.fopenSafer (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, q24, sv3]
  refine must_listed (o := 61) shaD_listing_ok.2.1 rfl hB4.done (hin _ (by decide)) hB4.mem.2.fopenSafer (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, q32, sv5]
  refine must_listed (o := 62) shaD_listing_ok.2.1 rfl hB4.done (hin _ (by decide)) hB4.mem.2.fopenSafer (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, q40, hretx]
  have hgx : x.g = s.g.opened := by
    rw [hgx]; simp only [callEntry_g]; rw [hg3, hgv, hfiles]; simp [jmpEntry, hg1, Proc.Ghost.opened]
  refine k _ fd ⟨rfl, ?_, ?_⟩ (Body.keep (u := x) hB4) hgx (by simpa [hrbx4] using hfx) hfd3 hfd31 (by simpa [hrbx4] using hnz) ?_ ?_ hB4.fs hB4.perm hLx
  · simp only [st_read_mk, Silmaril.Machine.RegisterFile.write_same]; rw [hB4.rsp]; bv_omega
  · intro r hr
    have hr' := hr
    simp only [Silmaril.X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · simp
    · simp
    · simp only [st_read_mk, Silmaril.Machine.RegisterFile.write_other, ne_eq, reduceCtorEq, not_false_eq_true]
      rw [st_regs_apply, hcs4 _ hr, h14_3]
    · simp only [st_read_mk, Silmaril.Machine.RegisterFile.write_other, ne_eq, reduceCtorEq, not_false_eq_true]
      rw [st_regs_apply, hcs4 _ hr, h15_3]
  · intro st0 h
    apply hnew st0
    have h' := file_push (v := b + 20140#64) (hfk1 _ st0 h) (by rw [hu8]; omega)
    simpa [jmpEntry, hrbx4] using h'
  · intro f st h
    have h1 : E.S.file w.m.memory f st := by rw [hmem3]; exact hO2 f st h
    exact hokx f st (by simp) (by rw [callEntry_mem]; exact file_push h1 (by rw [hw8]; omega))

end Silmaril.Elf.Link.Dyn.Sha256sum
