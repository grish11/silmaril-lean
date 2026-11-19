module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MemClose
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.Start
public import Silmaril.Raw.Elf.Link.Dyn.Proc.Frame
public import Silmaril.Elf.Link.Dyn.Streams.Defs

/-! # GNU `sha256sum`: `rpl_fclose` on output streams (and the close-path toolkit) -/

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

/-- The import at `a` is the named import `n` with contract `c`. -/
def ImpOk (W : World) (a : Word) (n : Name) (c : PState → Silmaril.X86.RelIsa.Res PState → Prop) : Prop :=
  ¬ W.InImage a.toNat ∧ a ≠ W.gate ∧ W.fns.find? (·.1 == a) = some (a, .named n) ∧ W.named n = c

theorem impOk_fn {W : World} {a : Word} {n : Name} {c : PState → Silmaril.X86.RelIsa.Res PState → Prop}
    (h : ImpOk W a n c) (s : PState) (r : Silmaril.X86.RelIsa.Res PState) : fnStep W (.named n) s r ↔ c s r := by
  simp only [fnStep, h.2.2.2]

/-- The imports the close path calls. -/
structure CloseImps (E : Env) (W : World) (b lb : Word) : Prop where
  lz : W.lazy = none
  img : W.InImage = ShaImg b
  hb : b.toNat + 0xa188 < 2 ^ 64
  fileno : ImpOk W (lb + 0x8ea80#64) (nm "fileno") (filenoStep E W)
  freading : ImpOk W (lb + 0x90790#64) (nm "__freading") (freadingStep E W)
  fflush : ImpOk W (lb + 0x858d0#64) (nm "fflush") (fflushStep E W)
  fclose : ImpOk W (lb + 0x85370#64) (nm "fclose") (fcloseStep E W)
  fpending : ImpOk W (lb + 0x90880#64) (nm "__fpending") (fpendingStep E W)

theorem sha_in' {W : World} {b : Word} (I : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64)
    {n : Nat} (hn : n < 0xa188) : W.InImage (b + BitVec.ofNat 64 n).toNat := by
  rw [I]; exact sha_in hb hn

theorem img_off {W : World} {b : Word} (I : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64)
    {c d : Nat} (h : c + d < 0xa188) : W.InImage (b + BitVec.ofNat 64 c + BitVec.ofNat 64 d).toNat := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact sha_in' I hb h

theorem file_push {E : Env} {m : Memory} {f : Word} {st : St} (h : E.S.file m f st) {sp v : Word}
    (hlo : E.S.lo ≤ (sp - 8#64).toNat) : E.S.file (pushMem m sp v) f st :=
  (E.S.local_ _ _ _ _ (pushMem_keeps fun x hx => Or.inl (by
    have := E.S.foot_lo _ _ _ _ h hx; omega)) h).1

/-- A push inside the room keeps the image. -/
theorem img_push {W : World} {b : Word} (I : W.InImage = ShaImg b) {m0 m : Memory} {sp sp' v : Word}
    {n : Nat} (hroom : Room W m0 sp n) (hlo : sp.toNat - n + 8 ≤ sp'.toNat) (hhi : sp'.toNat ≤ sp.toNat + 8) :
    Keeps (ShaImg b) m (pushMem m sp' v) := by
  apply pushMem_keeps
  intro x hx
  have h8 : (sp' - 8#64).toNat = sp'.toNat - 8 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; simp
  rw [h8]
  by_contra hc
  exact (hroom.2.2 x (by omega) (by omega)).2.2 (Or.inl (by rw [I]; exact hx))

theorem eval_ne_test {n : Nat} (x : BitVec n) :
    Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.logicFlagsN (x &&& x)) .ne =
      some (!decide (x = 0#n)) := by
  by_cases h : x = 0#n <;>
    simp [Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.logicFlagsN, Silmaril.X86.Ext.isZeroN, h,
      Silmaril.X86.Ext.kNot]

theorem eval_s_test {n : Nat} (x : BitVec n) :
    Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.logicFlagsN (x &&& x)) .s = some x.msb := by
  simp [Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.logicFlagsN]

/-- `test r32, r32` as the semantics builds it (the `and` instance at `Sz.d.bits`). -/
abbrev andD (x y : BitVec 32) : BitVec 32 :=
  @HAnd.hAnd (BitVec 32) (BitVec 32) (BitVec 32)
    (@instHAndOfAndOp (BitVec Silmaril.X86.Ext.Sz.d.bits) (@BitVec.instAndOp Silmaril.X86.Ext.Sz.d.bits)) x y

theorem eval_s_testD (x : BitVec 32) :
    Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.logicFlagsN (andD x x)) .s = some x.msb := eval_s_test x
theorem eval_e_testD (x : BitVec 32) :
    Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.logicFlagsN (andD x x)) .e = some (decide (x = 0#32)) :=
  Silmaril.X86.BlockCert9.eval_e_test x
theorem eval_ne_testD (x : BitVec 32) :
    Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.logicFlagsN (andD x x)) .ne = some (!decide (x = 0#32)) :=
  eval_ne_test x

theorem and20 {fl : BitVec 64} (h : fl.getLsbD 5 = false) :
    (BitVec.setWidth 32 fl &&& 32#32) = 0#32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat,
    show (32 : Nat) = 2 ^ 5 from rfl, Nat.testBit_two_pow]
  by_cases h5 : i = 5
  · subst h5
    have h' : fl[5] = false := by rw [← BitVec.getLsbD_eq_getElem]; exact h
    simp [h']
  · simp [Ne.symm h5]

/-- The image facts of the close path, preserved by keeping the image. -/
theorem shaMemC_keep {b lb : Word} {W : World} (I : W.InImage = ShaImg b) (hb : b.toNat + 0xa188 < 2 ^ 64) :
    ∀ m m', ShaMemC b lb m → Keeps W.InImage m m' → ShaMemC b lb m' :=
  fun _ _ hm h => hm.keep hb (by rw [I] at h; exact h)

/-- The streams other than the one at `rdi` keep their states from `s` to memory `m`. -/
def OK (E : Env) (s : PState) (m : Memory) : Prop :=
  ∀ f' st', f' ≠ s.m.core.read .rdi → E.S.file s.m.memory f' st' → E.S.file m f' st'

/-- A push inside the room keeps the caller's data. -/
theorem push_keeps_caller {W : World} {m0 m : Memory} {sp sp' v : Word} {n : Nat}
    (hroom : Room W m0 sp n) (hlo : sp.toNat - n + 8 ≤ sp'.toNat) (hhi : sp'.toNat ≤ sp.toNat) :
    Keeps (fun a => W.Kept a ∨ sp.toNat ≤ a) m (pushMem m sp' v) := by
  apply pushMem_keeps
  intro x hx
  have h8 : (sp' - 8#64).toNat = sp'.toNat - 8 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; simp
  rw [h8]
  rcases hx with hx | hx
  · by_contra hc
    exact (hroom.2.2 x (by omega) (by omega)).2.2 hx
  · omega

/-- The word pushed at `sp`, read back after later pushes below it. -/
theorem push_read_after {m : Memory} {sp v : Word} (hr : m.Permitted .read (sp - 8#64).toNat 8)
    (hw : m.Permitted .write (sp - 8#64).toNat 8) (h8 : (sp - 8#64).toNat = sp.toNat - 8) :
    (pushMem m sp v).readBytes (sp.toNat - 8) 8 = some (Silmaril.Machine.LittleEndian.encodeWords [v]) := by
  rw [← h8]; exact pushMem_read hr hw

theorem read_push_other {m : Memory} {sp v : Word} {a : Nat} (h8 : (sp - 8#64).toNat = sp.toNat - 8)
    (h : a + 8 ≤ sp.toNat - 8 ∨ sp.toNat ≤ a) (hs : 8 ≤ sp.toNat) :
    (pushMem m sp v).readBytes a 8 = m.readBytes a 8 :=
  (pushMem_keeps (P := fun x => x < sp.toNat - 8 ∨ sp.toNat ≤ x) fun x hx => by rw [h8]; omega).readBytes
    (fun k hk => by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- **`rpl_fclose`** (`0x42b0`) on an output stream with no error, writes reliable. -/
theorem sha_rplFclose_out {E : Env} {W : World} {b lb : Word} (I : CloseImps E W b lb) {Q : PState → Prop}
    {s : PState} (hrip : s.m.core.rip = b + 0x42b0#64) (habi : AbiEntry s.m.core s.m.memory)
    (hroom : Room W s.m.memory (s.m.core.read .rsp) 256) (hlo : E.S.lo + 256 ≤ (s.m.core.read .rsp).toNat)
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
  have hl := hm.rplFclose
  have hm1 : ShaMemC b lb (pushMem s.m.memory (s.m.core.read .rsp) (s.m.core.read .rbp)) :=
    hm.keep I.hb (img_push I.img hroom (by omega) (by omega))
  have hm2 : ShaMemC b lb (pushMem (pushMem s.m.memory (s.m.core.read .rsp) (s.m.core.read .rbp))
      (s.m.core.read .rsp - 8#64) (s.m.core.read .r13)) :=
    hm1.keep I.hb (img_push I.img hroom (by omega) (by omega))
  have hm3 : ShaMemC b lb (pushMem (pushMem (pushMem s.m.memory (s.m.core.read .rsp) (s.m.core.read .rbp))
      (s.m.core.read .rsp - 8#64) (s.m.core.read .r13)) (s.m.core.read .rsp - 8#64 - 8#64) (s.m.core.read .r12)) :=
    hm2.keep I.hb (img_push I.img hroom (by omega) (by omega))
  have hm4 : ShaMemC b lb (pushMem (pushMem (pushMem (pushMem s.m.memory (s.m.core.read .rsp) (s.m.core.read .rbp))
      (s.m.core.read .rsp - 8#64) (s.m.core.read .r13)) (s.m.core.read .rsp - 8#64 - 8#64) (s.m.core.read .r12))
      (s.m.core.read .rsp - 8#64 - 8#64 - 8#64) (s.m.core.read .rbx)) :=
    hm3.keep I.hb (img_push I.img hroom (by omega) (by omega))
  refine must_listed (o := 0) shaC_listing_ok.2.1 rfl hd (by rw [hrip]; exact hin _ (by decide)) hl
    (by rw [hrip]; exact (BitVec.add_zero _).symm) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa using p1)]
  xstep [hrip]
  refine must_listed (o := 1) shaC_listing_ok.2.1 rfl hd (hin _ (by decide)) hm1.rplFclose (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 4) shaC_listing_ok.2.1 rfl hd (hin _ (by decide)) hm1.rplFclose (by rw [ripadd]) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa [pushMem_permitted] using p2)]
  xstep []
  refine must_listed (o := 6) shaC_listing_ok.2.1 rfl hd (hin _ (by decide)) hm2.rplFclose (by rw [ripadd]) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa [pushMem_permitted] using p3)]
  xstep []
  refine must_listed (o := 8) shaC_listing_ok.2.1 rfl hd (hin _ (by decide)) hm3.rplFclose (by rw [ripadd]) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa [pushMem_permitted] using p4)]
  xstep []
  refine must_listed (o := 9) shaC_listing_ok.2.1 rfl hd (hin _ (by decide)) hm4.rplFclose (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 12) shaC_listing_ok.2.1 rfl hd (hin _ (by decide)) hm4.rplFclose (by rw [ripadd]) ?_
  xstep []
  -- the body, from here on an opaque state
  let sv : List (Nat × Word) := [(8, s.m.core.read .rbp), (16, s.m.core.read .r13), (24, s.m.core.read .r12),
    (32, s.m.core.read .rbx)]
  refine must_gen (fun u => Body W (ShaMemC b lb) s u 40 256 sv ∧ u.m.core.rip = b + 0x42c0#64 ∧
      u.m.core.read .rbx = s.m.core.read .rdi ∧ u.m.core.read .rdi = s.m.core.read .rdi ∧
      u.m.core.read .rbp = s.m.core.read .rsp - 8#64 ∧ u.m.core.read .r12 = s.m.core.read .r12 ∧
      u.m.core.read .r13 = s.m.core.read .r13 ∧ u.m.core.read .r14 = s.m.core.read .r14 ∧
      u.m.core.read .r15 = s.m.core.read .r15 ∧ u.g = s.g ∧ E.S.file u.m.memory (s.m.core.read .rdi) st ∧
      OK E s u.m.memory) ?_ ?_
  · have r1 : s.m.memory.Permitted .read (s.m.core.read .rsp - 8#64).toNat 8 :=
      room_perm hroom (Or.inl rfl) (by omega) (by omega)
    have r2 : s.m.memory.Permitted .read (s.m.core.read .rsp - 8#64 - 8#64).toNat 8 :=
      room_perm hroom (Or.inl rfl) (by omega) (by omega)
    have r3 : s.m.memory.Permitted .read (s.m.core.read .rsp - 8#64 - 8#64 - 8#64).toNat 8 :=
      room_perm hroom (Or.inl rfl) (by omega) (by omega)
    have r4 : s.m.memory.Permitted .read (s.m.core.read .rsp - 8#64 - 8#64 - 8#64 - 8#64).toNat 8 :=
      room_perm hroom (Or.inl rfl) (by omega) (by omega)
    refine ⟨⟨?_, ?_, hroom.pushMem.pushMem.pushMem.pushMem, hm4, rfl, hd, ?_,
      fun a _ _ acc => by simp [pushMem_permits]⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_⟩
    · simp; bv_omega
    · exact keepF ((((push_keeps_caller hroom (by omega) (by omega)).trans
        (push_keeps_caller hroom (by rw [e8]; omega) (by rw [e8]; omega))).trans
        (push_keeps_caller hroom (by rw [e16]; omega) (by rw [e16]; omega))).trans
        (push_keeps_caller hroom (by rw [e24]; omega) (by rw [e24]; omega)))
    · intro p hp
      simp only [sv, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · simp only
        rw [read_push_other (by rw [e32, e24]; omega) (by rw [e24]; omega) (by rw [e24]; omega),
          read_push_other (by rw [e24, e16]; omega) (by rw [e16]; omega) (by rw [e16]; omega),
          read_push_other (by rw [e16, e8]; omega) (by rw [e8]; omega) (by rw [e8]; omega)]
        exact push_read_after r1 p1 e8
      · simp only
        rw [read_push_other (by rw [e32, e24]; omega) (by rw [e24]; omega) (by rw [e24]; omega),
          read_push_other (by rw [e24, e16]; omega) (by rw [e16]; omega) (by rw [e16]; omega),
          show (s.m.core.read .rsp).toNat - 16 = (s.m.core.read .rsp - 8#64).toNat - 8 by rw [e8]; omega]
        exact push_read_after (by simpa [pushMem_permitted] using r2) (by simpa [pushMem_permitted] using p2) (by rw [e16, e8]; omega)
      · simp only
        rw [read_push_other (by rw [e32, e24]; omega) (by rw [e24]; omega) (by rw [e24]; omega),
          show (s.m.core.read .rsp).toNat - 24 = (s.m.core.read .rsp - 8#64 - 8#64).toNat - 8 by rw [e16]; omega]
        exact push_read_after (by simpa [pushMem_permitted] using r3) (by simpa [pushMem_permitted] using p3) (by rw [e24, e16]; omega)
      · simp only
        rw [show (s.m.core.read .rsp).toNat - 32 = (s.m.core.read .rsp - 8#64 - 8#64 - 8#64).toNat - 8 by rw [e24]; omega]
        exact push_read_after (by simpa [pushMem_permitted] using r4) (by simpa [pushMem_permitted] using p4) (by rw [e32, e24]; omega)
    · rfl
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp
    · exact file_push (file_push (file_push (file_push hf (by rw [e8]; omega)) (by rw [e16]; omega))
        (by rw [e24]; omega)) (by rw [e32]; omega)
    · intro f' st' _ h
      exact file_push (file_push (file_push (file_push h (by rw [e8]; omega)) (by rw [e16]; omega))
        (by rw [e24]; omega)) (by rw [e32]; omega)
  rintro u ⟨hB, hrip1, hrbx, hrdi, hrbp, hr12, hr13, hr14, hr15, hg, hf1, hO1⟩
  have hsv : ∀ p ∈ sv, p.1 ≤ 32 ∧ 32 ≤ 40 := by
    intro p hp
    simp only [sv, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> simp
  have hal40 : ((s.m.core.read .rsp).toNat - 40) % 16 = 0 := by omega
  have hu8 : E.S.lo ≤ (u.m.core.read .rsp - 8#64).toNat := by
    rw [hB.rsp, sub_toNat (k := 8) (by rw [sub_toNat (by omega) (by decide)]; omega) (by decide),
      sub_toNat (by omega) (by decide)]; omega
  -- fileno (f)
  refine body_call (shaMemC_keep I.img I.hb) hB (by decide) (by decide) hsv hal40 I.lz
    (o := 16) (so := 0x180) (pb := b + 0x23c0#64) (fp := fun _ => False)
    shaC_listing_ok.2.1 rfl (by rw [hrip1]; exact hin _ (by decide)) (fun m h => h.rplFclose)
    (by rw [hrip1, ripadd]) shaC_listing_ok.1 rfl rfl (by simp only [BitVec.add_assoc]; rfl)
    (img_off I.img I.hb (by decide)) (img_off I.img I.hb (by decide)) (fun m h => h.plt)
    (fun m h => by
      rw [show b + 0x23c0#64 + BitVec.ofNat 64 (0x180 + 4 + 6) + BitVec.signExtend 64 0x794e#32 = b + 0x9e98#64 by
        simp only [BitVec.add_assoc]; rfl]
      exact h.fileno)
    I.fileno.1 I.fileno.2.1 I.fileno.2.2.1 (fun r h => (impOk_fn I.fileno _ r).1 h)
    (fun he => ⟨he, st, by rw [callEntry_mem, callEntry_read _ _ _ (by decide), hrdi]; exact file_push hf1 hu8⟩)
    (fun v hv => ⟨hv.1.1, hv.1.2.2.1, by simpa [callEntry] using hv.1.2.1,
      by rw [hv.2.1]; exact hB.done⟩)
    (fun x h => h.elim) (fun x h => h.elim) ?_
  intro v hv hB2 hrip2 hrsp2 hcs2
  obtain ⟨-, hgv, hok2, hfdf⟩ := hv
  have hfE2 := file_push (v := b + 0x42b0#64 + BitVec.ofNat 64 (16 + 5)) hf1 hu8
  have hfdv : low32 (v.m.core.read .rax) = BitVec.ofNat 32 st.fd :=
    hfdf st (by rw [callEntry_mem, callEntry_read _ _ _ (by decide), hrdi]; exact hfE2)
  have hf2 : E.S.file v.m.memory (s.m.core.read .rdi) st :=
    hok2 _ st (by simp) (by rw [callEntry_mem]; exact hfE2)
  have hO2 : OK E s v.m.memory := fun f' st' hne h =>
    hok2 _ st' (by simp) (by rw [callEntry_mem]; exact file_push (hO1 f' st' hne h) hu8)
  have hrbx2 : v.m.core.read .rbx = s.m.core.read .rdi := by
    rw [hcs2 .rbx (by simp [Silmaril.X86.sysv64_calleeSaved]), hrbx]
  refine must_listed (o := 21) shaC_listing_ok.2.1 rfl hB2.done (by rw [hrip2]; exact img_off I.img I.hb (by decide))
    hB2.mem.rplFclose (by rw [hrip2]) ?_
  xstep [hrip2]
  refine must_listed (o := 24) shaC_listing_ok.2.1 rfl hB2.done (hin _ (by decide))
    hB2.mem.rplFclose (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 26) shaC_listing_ok.2.1 rfl hB2.done (hin _ (by decide))
    hB2.mem.rplFclose (by rw [ripadd]) ?_
  have hfd' : BitVec.setWidth 32 (v.m.core.read .rax) = BitVec.ofNat 32 st.fd := hfdv
  have hmsb : (BitVec.ofNat 32 st.fd).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  have hs : Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.logicFlagsN (BitVec.ofNat 32 st.fd &&& BitVec.ofNat 32 st.fd))
      .s = some false := by rw [eval_s_test, hmsb]
  xstep [eval_s_testD, hfd', hmsb]
  refine must_gen (fun u => Body W (ShaMemC b lb) s u 40 256 sv ∧ u.m.core.rip = b + 0x42cc#64 ∧
      u.m.core.read .rdi = s.m.core.read .rdi ∧ u.m.core.read .rbx = s.m.core.read .rdi ∧
      u.m.core.read .rsp = v.m.core.read .rsp ∧ u.g = v.g ∧ E.S.file u.m.memory (s.m.core.read .rdi) st ∧
      u.m.core.read .r14 = s.m.core.read .r14 ∧ u.m.core.read .r15 = s.m.core.read .r15 ∧ OK E s u.m.memory)
    ?_ ?_
  · exact ⟨hB2.of_eq rfl (by simp) rfl rfl, rfl, by simp [hrbx2], by simp [hrbx2], by simp, rfl, hf2,
      by simp [hcs2 .r14 (by simp [Silmaril.X86.sysv64_calleeSaved]), hr14],
      by simp [hcs2 .r15 (by simp [Silmaril.X86.sysv64_calleeSaved]), hr15], hO2⟩
  rintro v2 ⟨hB2', hrip2', hrdi2', hrbx2', hrsp2', hg2', hf2', h14_2, h15_2, hO2'⟩
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
    (fun w hw => ⟨hw.1.1, hw.1.2.2.1, by simpa [callEntry] using hw.1.2.1,
      by rw [hw.2.1]; exact hB2'.done⟩)
    (fun x h => h.elim) (fun x h => h.elim) ?_
  intro v3 hv3 hB3 hrip3 hrsp3 hcs3
  obtain ⟨-, hgv3, hok3, hrd3⟩ := hv3
  have hfE3 := file_push (v := b + 0x42b0#64 + BitVec.ofNat 64 (28 + 5)) hf2' hv8
  have hz3 : BitVec.setWidth 32 (v3.m.core.read .rax) = 0#32 :=
    (hrd3 st (by rw [callEntry_mem, callEntry_read _ _ _ (by decide), hrdi2']; exact hfE3)).2 hr
  have hf3 : E.S.file v3.m.memory (s.m.core.read .rdi) st :=
    hok3 _ st (by simp) (by rw [callEntry_mem]; exact hfE3)
  have hO3 : OK E s v3.m.memory := fun f' st' hne h =>
    hok3 _ st' (by simp) (by rw [callEntry_mem]; exact file_push (hO2' f' st' hne h) hv8)
  have hrbx3 : v3.m.core.read .rbx = s.m.core.read .rdi := by
    rw [hcs3 .rbx (by simp [Silmaril.X86.sysv64_calleeSaved]), hrbx2']
  refine must_listed (o := 33) shaC_listing_ok.2.1 rfl hB3.done (by rw [hrip3]; exact img_off I.img I.hb (by decide))
    hB3.mem.rplFclose (by rw [hrip3]) ?_
  xstep [hrip3]
  refine must_listed (o := 35) shaC_listing_ok.2.1 rfl hB3.done (hin _ (by decide))
    hB3.mem.rplFclose (by rw [ripadd]) ?_
  xstep [eval_ne_testD, hz3]
  refine must_listed (o := 37) shaC_listing_ok.2.1 rfl hB3.done (hin _ (by decide))
    hB3.mem.rplFclose (by rw [ripadd]) ?_
  xstep []
  refine must_gen (fun u => Body W (ShaMemC b lb) s u 40 256 sv ∧ u.m.core.rip = b + 0x42d8#64 ∧
      u.m.core.read .rdi = s.m.core.read .rdi ∧ u.m.core.read .rbx = s.m.core.read .rdi ∧
      u.m.core.read .rsp = v3.m.core.read .rsp ∧ u.g = v3.g ∧ E.S.file u.m.memory (s.m.core.read .rdi) st ∧
      u.m.core.read .r14 = s.m.core.read .r14 ∧ u.m.core.read .r15 = s.m.core.read .r15 ∧ OK E s u.m.memory)
    ?_ ?_
  · exact ⟨hB3.of_eq rfl (by simp) rfl rfl, rfl, by simp [hrbx3], by simp [hrbx3], by simp, rfl, hf3,
      by simp [hcs3 .r14 (by simp [Silmaril.X86.sysv64_calleeSaved]), h14_2],
      by simp [hcs3 .r15 (by simp [Silmaril.X86.sysv64_calleeSaved]), h15_2], hO3⟩
  rintro v4 ⟨hB4, hrip4, hrdi4, hrbx4, hrsp4, hg4, hf4, h14_4, h15_4, hO4⟩
  -- __freading (f), again
  have hv8' : E.S.lo ≤ (v4.m.core.read .rsp - 8#64).toNat := by rw [hrsp4, hrsp3, hrsp2', hrsp2]; exact hu8
  refine body_call (shaMemC_keep I.img I.hb) hB4 (by decide) (by decide) hsv hal40 I.lz
    (o := 40) (so := 0x110) (pb := b + 0x23c0#64) (fp := fun _ => False)
    shaC_listing_ok.2.1 rfl (by rw [hrip4]; exact hin _ (by decide)) (fun m h => h.rplFclose)
    (by rw [hrip4, ripadd]) shaC_listing_ok.1 rfl rfl (by simp only [BitVec.add_assoc]; rfl)
    (img_off I.img I.hb (by decide)) (img_off I.img I.hb (by decide)) (fun m h => h.plt)
    (fun m h => by
      rw [show b + 0x23c0#64 + BitVec.ofNat 64 (0x110 + 4 + 6) + BitVec.signExtend 64 0x7986#32 = b + 0x9e60#64 by
        simp only [BitVec.add_assoc]; rfl]
      exact h.freading)
    I.freading.1 I.freading.2.1 I.freading.2.2.1 (fun r h => (impOk_fn I.freading _ r).1 h)
    (fun he => ⟨he, st, by rw [callEntry_mem, callEntry_read _ _ _ (by decide), hrdi4]; exact file_push hf4 hv8'⟩)
    (fun w hw => ⟨hw.1.1, hw.1.2.2.1, by simpa [callEntry] using hw.1.2.1,
      by rw [hw.2.1]; exact hB4.done⟩)
    (fun x h => h.elim) (fun x h => h.elim) ?_
  intro v5 hv5 hB5 hrip5 hrsp5 hcs5
  obtain ⟨-, hgv5, hok5, hrd5⟩ := hv5
  have hfE5 := file_push (v := b + 0x42b0#64 + BitVec.ofNat 64 (40 + 5)) hf4 hv8'
  have hz5 : BitVec.setWidth 32 (v5.m.core.read .rax) = 0#32 :=
    (hrd5 st (by rw [callEntry_mem, callEntry_read _ _ _ (by decide), hrdi4]; exact hfE5)).2 hr
  have hf5 : E.S.file v5.m.memory (s.m.core.read .rdi) st :=
    hok5 _ st (by simp) (by rw [callEntry_mem]; exact hfE5)
  have hO5 : OK E s v5.m.memory := fun f' st' hne h =>
    hok5 _ st' (by simp) (by rw [callEntry_mem]; exact file_push (hO4 f' st' hne h) hv8')
  have hrbx5 : v5.m.core.read .rbx = s.m.core.read .rdi := by
    rw [hcs5 .rbx (by simp [Silmaril.X86.sysv64_calleeSaved]), hrbx4]
  refine must_listed (o := 45) shaC_listing_ok.2.1 rfl hB5.done (by rw [hrip5]; exact img_off I.img I.hb (by decide))
    hB5.mem.rplFclose (by rw [hrip5]) ?_
  xstep [hrip5]
  refine must_listed (o := 47) shaC_listing_ok.2.1 rfl hB5.done (hin _ (by decide))
    hB5.mem.rplFclose (by rw [ripadd]) ?_
  xstep [eval_ne_testD, hz5]
  refine must_listed (o := 49) shaC_listing_ok.2.1 rfl hB5.done (hin _ (by decide))
    hB5.mem.rplFclose (by rw [ripadd]) ?_
  xstep []
  refine must_gen (fun u => Body W (ShaMemC b lb) s u 40 256 sv ∧ u.m.core.rip = b + 0x42e4#64 ∧
      u.m.core.read .rdi = s.m.core.read .rdi ∧ u.m.core.read .rbx = s.m.core.read .rdi ∧
      u.m.core.read .rsp = v5.m.core.read .rsp ∧ u.g = v5.g ∧ E.S.file u.m.memory (s.m.core.read .rdi) st ∧
      u.m.core.read .r14 = s.m.core.read .r14 ∧ u.m.core.read .r15 = s.m.core.read .r15 ∧ OK E s u.m.memory)
    ?_ ?_
  · exact ⟨hB5.of_eq rfl (by simp) rfl rfl, rfl, by simp [hrbx5], by simp [hrbx5], by simp, rfl, hf5,
      by simp [hcs5 .r14 (by simp [Silmaril.X86.sysv64_calleeSaved]), h14_4],
      by simp [hcs5 .r15 (by simp [Silmaril.X86.sysv64_calleeSaved]), h15_4], hO5⟩
  rintro v6 ⟨hB6, hrip6, hrdi6, hrbx6, hrsp6, hg6, hf6, h14_6, h15_6, hO6⟩
  have hg6s : v6.g = s.g := by
    rw [hg6, hgv5]; simp only [callEntry_g]; rw [hg4, hgv3]; simp only [callEntry_g]
    rw [hg2', hgv]; simp only [callEntry_g]; exact hg
  -- fflush (f)
  have hv86 : E.S.lo ≤ (v6.m.core.read .rsp - 8#64).toNat := by
    rw [hrsp6, hrsp5, hrsp4, hrsp3, hrsp2', hrsp2]; exact hu8
  refine body_call (shaMemC_keep I.img I.hb) hB6 (by decide) (by decide) hsv hal40 I.lz
    (o := 52) (so := 0x1e0) (pb := b + 0x23c0#64) (fp := fun _ => False)
    shaC_listing_ok.2.1 rfl (by rw [hrip6]; exact hin _ (by decide)) (fun m h => h.rplFclose)
    (by rw [hrip6, ripadd]) shaC_listing_ok.1 rfl rfl (by simp only [BitVec.add_assoc]; rfl)
    (img_off I.img I.hb (by decide)) (img_off I.img I.hb (by decide)) (fun m h => h.plt)
    (fun m h => by
      rw [show b + 0x23c0#64 + BitVec.ofNat 64 (0x1e0 + 4 + 6) + BitVec.signExtend 64 0x791e#32 = b + 0x9ec8#64 by
        simp only [BitVec.add_assoc]; rfl]
      exact h.fflush)
    I.fflush.1 I.fflush.2.1 I.fflush.2.2.1 (fun r h => (impOk_fn I.fflush _ r).1 h)
    (fun he => ⟨he, st, by rw [callEntry_mem, callEntry_read _ _ _ (by decide), hrdi6]; exact file_push hf6 hv86⟩)
    (fun w hw => ⟨hw.1.1, hw.1.2.2.1, by simpa [callEntry] using hw.1.2.1, hw.2.1.2.2.1⟩)
    (fun x h => h.elim) (fun x h => h.elim) ?_
  intro v7 hv7 hB7 hrip7 hrsp7 hcs7
  obtain ⟨-, ⟨hj7, ha7, hd7, hi7, he7⟩, hok7, hfl7⟩ := hv7
  have hfE7 := file_push (v := b + 0x42b0#64 + BitVec.ofNat 64 (52 + 5)) hf6 hv86
  have hO7 : OK E s v7.m.memory := fun f' st' hne h =>
    hok7 _ st' (by rw [callEntry_read _ _ _ (by decide), hrdi6]; simpa using hne)
      (by rw [callEntry_mem]; exact file_push (hO6 f' st' hne h) hv86)
  have hfl := hfl7 st (by rw [callEntry_mem, callEntry_read _ _ _ (by decide), hrdi6]; exact hfE7)
  have hres : BitVec.setWidth 32 (v7.m.core.read .rax) = 0#32 ∧
      E.S.file v7.m.memory (s.m.core.read .rdi) { st with buf := [] } ∧
      v7.g.out = s.g.out ++ (if st.fd = 1 then st.buf else []) := by
    by_cases h1 : st.fd = 1
    · rcases hfl.1 h1 with ⟨ho, hf, hz⟩ | ⟨hu, -⟩
      · refine ⟨hz he, by simpa [hrdi6, callEntry_read _ _ _ (show Reg.rdi ≠ .rsp by decide)] using hf, ?_⟩
        rw [ho]; simp [h1, hg6s]
      · rw [hrel] at hu; cases hu
    · obtain ⟨ho, hf, hz⟩ := hfl.2 h1
      refine ⟨hz he, by simpa [hrdi6, callEntry_read _ _ _ (show Reg.rdi ≠ .rsp by decide)] using hf, ?_⟩
      rw [ho, ite_eq_right_iff.mpr (fun h => absurd h h1)]; simp [hg6s]
  obtain ⟨hz7, hf7, ho7⟩ := hres
  have hrbx7 : v7.m.core.read .rbx = s.m.core.read .rdi := by
    rw [hcs7 .rbx (by simp [Silmaril.X86.sysv64_calleeSaved]), hrbx6]
  refine must_listed (o := 57) shaC_listing_ok.2.1 rfl hB7.done (by rw [hrip7]; exact img_off I.img I.hb (by decide))
    hB7.mem.rplFclose (by rw [hrip7]) ?_
  xstep [hrip7]
  refine must_listed (o := 59) shaC_listing_ok.2.1 rfl hB7.done (hin _ (by decide))
    hB7.mem.rplFclose (by rw [ripadd]) ?_
  xstep [eval_e_testD, hz7]
  refine must_listed (o := 132) shaC_listing_ok.2.1 rfl hB7.done (hin _ (by decide))
    hB7.mem.rplFclose (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 135) shaC_listing_ok.2.1 rfl hB7.done (hin _ (by decide))
    hB7.mem.rplFclose (by rw [ripadd]) ?_
  xstep []
  have hv7r : (v7.m.core.read .rsp).toNat = (s.m.core.read .rsp).toNat - 40 := by
    rw [hB7.rsp]; exact sub_toNat (by omega) (by decide)
  have q8 : ((v7.m.core.read .rsp).toNat + 8) % 18446744073709551616 = (s.m.core.read .rsp).toNat - 32 := by
    rw [hv7r]; omega
  have q16 : ((v7.m.core.read .rsp).toNat + 16) % 18446744073709551616 = (s.m.core.read .rsp).toNat - 24 := by
    rw [hv7r]; omega
  have q24 : ((v7.m.core.read .rsp).toNat + 24) % 18446744073709551616 = (s.m.core.read .rsp).toNat - 16 := by
    rw [hv7r]; omega
  have q32 : ((v7.m.core.read .rsp).toNat + 32) % 18446744073709551616 = (s.m.core.read .rsp).toNat - 8 := by
    rw [hv7r]; omega
  have sv1 := hB7.saved (32, s.m.core.read .rbx) (by simp [sv])
  have sv2 := hB7.saved (24, s.m.core.read .r12) (by simp [sv])
  have sv3 := hB7.saved (16, s.m.core.read .r13) (by simp [sv])
  have sv4 := hB7.saved (8, s.m.core.read .rbp) (by simp [sv])
  simp only at sv1 sv2 sv3 sv4
  refine must_listed (o := 139) shaC_listing_ok.2.1 rfl hB7.done (hin _ (by decide))
    hB7.mem.rplFclose (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, q8, sv1]
  refine must_listed (o := 140) shaC_listing_ok.2.1 rfl hB7.done (hin _ (by decide))
    hB7.mem.rplFclose (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, q16, sv2]
  refine must_listed (o := 142) shaC_listing_ok.2.1 rfl hB7.done (hin _ (by decide))
    hB7.mem.rplFclose (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, q24, sv3]
  refine must_listed (o := 144) shaC_listing_ok.2.1 rfl hB7.done (hin _ (by decide))
    hB7.mem.rplFclose (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, q32, sv4]
  have h14_7 : v7.m.core.read .r14 = s.m.core.read .r14 := by
    rw [hcs7 .r14 (by simp [Silmaril.X86.sysv64_calleeSaved]), h14_6]
  have h15_7 : v7.m.core.read .r15 = s.m.core.read .r15 := by
    rw [hcs7 .r15 (by simp [Silmaril.X86.sysv64_calleeSaved]), h15_6]
  have hsp40 : v7.m.core.read .rsp + 40#64 = s.m.core.read .rsp := by
    rw [hB7.rsp]; exact BitVec.sub_add_cancel _ _
  have hretk : v7.m.memory.readBytes (s.m.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [Silmaril.X86.FnContract.retOf s.m.core s.m.memory]) := by
    rw [(Body.keep hB7).readBytes (fun j hj => Or.inr (by omega))]; exact habi.returnAddress
  have hg7s : v7.g.jobs = s.g.jobs ∧ v7.g.atexit = s.g.atexit ∧ v7.g.inp = s.g.inp ∧ v7.g.err = s.g.err := by
    simp only [callEntry_g] at hj7 ha7 hi7 he7; rw [hg6s] at hj7 ha7 hi7 he7; exact ⟨hj7, ha7, hi7, he7.1⟩
  -- the tail call fclose (f)
  refine must_plt_jmp (o := 145) (so := 0x160) (pb := b + 0x23c0#64) hd7 I.lz shaC_listing_ok.2.1 rfl
    (hin _ (by decide)) hB7.mem.rplFclose (by rw [ripadd]) shaC_listing_ok.1 rfl rfl
    (by simp only [BitVec.add_assoc]; rfl)
    (img_off I.img I.hb (by decide)) (img_off I.img I.hb (by decide)) hB7.mem.plt
    (by
      rw [show b + 0x23c0#64 + BitVec.ofNat 64 (0x160 + 4 + 6) + BitVec.signExtend 64 0x795e#32 = b + 0x9e88#64 by
        simp only [BitVec.add_assoc]; rfl]
      exact hB7.mem.fclose)
    I.fclose.1 I.fclose.2.1 I.fclose.2.2.1 (fun r h => (impOk_fn I.fclose _ r).1 h)
    ⟨abiEntry_of (v := Silmaril.X86.FnContract.retOf s.m.core s.m.memory)
        (by simp [jmpEntry, hsp40]; exact habi.aligned) (by simpa [jmpEntry, hsp40] using hretk),
      _, by simpa [jmpEntry, hrbx7] using hf7⟩ ?_
  rintro t ⟨⟨⟨habiT, hkT⟩, hfsT, hspT, -, -⟩, hjT, haT, hdT, hiT, heT, -, -, -, hokT, hclT⟩
  have hcl := hclT _ (by simpa [jmpEntry, hrbx7] using hf7)
  have hgT : t.g.out = s.g.out ++ (if st.fd = 1 then st.buf else []) ∧ low32 (t.m.core.read .rax) = 0#32 := by
    simp only [jmpEntry] at hcl ⊢
    by_cases h1 : st.fd = 1
    · rcases hcl.1 h1 with ⟨ho, hz⟩ | ⟨hu, -⟩
      · exact ⟨by rw [ho, ho7]; simp, hz he⟩
      · rw [hrel] at hu; cases hu
    · obtain ⟨ho, hz⟩ := hcl.2 h1
      exact ⟨by rw [ho, ho7], hz he⟩
  refine k t ⟨?_, ?_, ?_⟩ ?_ hgT.1 ?_ ?_ hdT ?_ ?_ hgT.2 ?_ ?_
  · rw [habiT.pc]; exact retOf_of (by simpa [jmpEntry, hsp40] using hretk)
  · rw [habiT.stack]; simp [jmpEntry, hsp40]
  · intro r hr
    rw [habiT.calleeSaved r hr]
    simp only [Silmaril.X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [jmpEntry, h14_7, h15_7]
  · refine (Body.keep hB7).trans (hkT.mono fun x hx => ⟨?_, fun h => h⟩)
    rcases hx with h | h
    · exact Or.inl h
    · right; simp [jmpEntry, hsp40]; omega
  · rw [hjT]; exact hg7s.1
  · rw [haT]; exact hg7s.2.1
  · rw [hiT]; exact hg7s.2.2.1
  · rw [heT]; exact hg7s.2.2.2
  · intro f' st' hne h
    exact hokT f' st' (by simpa [jmpEntry, hrbx7] using hne) (by simpa [jmpEntry] using hO7 f' st' hne h)
  · intro x h1 h2 acc
    unfold StackPerm at hspT
    simp only [jmpEntry, st_read_mk, Silmaril.Machine.RegisterFile.write_same,
      Silmaril.Machine.RegisterFile.write_other, ne_eq, reduceCtorEq, not_false_eq_true, hsp40] at hspT
    rw [hspT x (range_mb h1 h2).1 (range_mb h1 h2).2 acc]
    exact hB7.perm x h1 h2 acc

/-! ## Library variables a run keeps (`LibK`)

`LibV E W m0`: the mapped, non-private bytes of `m0` below the streams outside the program's kept
memory: the library's own variables (`program_invocation_name`, …). Every library call keeps them
unless they are in its footprint (`LibRet`, `FreeRet`), and the program writes only its stack, its
image and its heap blocks. `LibK E W m0 m`: they are as in `m0` and still non-private. -/

/-- The library variables of `m0`. -/
def LibV (E : Env) (W : World) (m0 : Memory) (a : Nat) : Prop :=
  a < E.S.lo ∧ ¬ W.Kept a ∧ ¬ E.S.priv m0 a ∧ m0.permits .read a = true

/-- The library variables of `m0` are kept up to `m` and still non-private. -/
def LibK (E : Env) (W : World) (m0 m : Memory) : Prop :=
  Keeps (LibV E W m0) m0 m ∧ ∀ a, LibV E W m0 a → ¬ E.S.priv m a

theorem LibK.refl (E : Env) (W : World) (m : Memory) : LibK E W m m :=
  ⟨Keeps.refl _ _, fun _ ha => ha.2.2.1⟩

theorem LibK.of_eq {E : Env} {W : World} {m0 m m' : Memory} (h : LibK E W m0 m) (he : m' = m) :
    LibK E W m0 m' := he ▸ h

/-- A library variable of `m0` is one of `m` when `LibK m0 m`. -/
theorem LibK.libV {E : Env} {W : World} {m0 m : Memory} (h : LibK E W m0 m) {a : Nat}
    (ha : LibV E W m0 a) : LibV E W m a :=
  ⟨ha.1, ha.2.1, h.2 a ha, by rw [(h.1 a ha).2]; exact ha.2.2.2⟩

theorem LibK.trans {E : Env} {W : World} {m0 m1 m2 : Memory} (h1 : LibK E W m0 m1)
    (h2 : LibK E W m1 m2) : LibK E W m0 m2 :=
  ⟨h1.1.trans (h2.1.mono fun _ ha => h1.libV ha), fun a ha => h2.2 a (h1.libV ha)⟩

/-- A change of memory at and above `lo` (the program's stack) keeps `LibK`. -/
theorem LibK.high {E : Env} {W : World} {m0 m m' : Memory} (h : LibK E W m0 m)
    (hk : Keeps (fun a => a < E.S.lo) m m') : LibK E W m0 m' := by
  have hp : E.S.priv m' = E.S.priv m := E.S.priv_local _ _ fun a ha => hk a ha
  exact ⟨h.1.trans (hk.mono fun a ha => ha.1), fun a ha => by rw [hp]; exact h.2 a ha⟩

/-- A store or push at `sp` above `lo` keeps `LibK`. -/
theorem LibK.push {E : Env} {W : World} {m0 m : Memory} (h : LibK E W m0 m) {sp v : Word}
    (hlo : E.S.lo ≤ (sp - 8#64).toNat) : LibK E W m0 (pushMem m sp v) :=
  h.high (pushMem_keeps fun x hx => Or.inl (by omega))

/-- **A library call keeps `LibK`** when its footprint `fp` holds no library variable of `m0`:
it keeps the mapped non-private bytes outside `fp` and makes private only unmapped bytes or `fp`. -/
theorem LibK.lib {E : Env} {W : World} {m0 m1 m2 : Memory} (h : LibK E W m0 m1) {fp : Nat → Prop}
    (hk : Keeps (fun a => ¬ E.S.priv m1 a ∧ ¬ fp a ∧ m1.permits .read a = true) m1 m2)
    (hpg : ∀ a, E.S.priv m2 a → E.S.priv m1 a ∨ m1.permits .read a = false ∨ fp a)
    (hF : ∀ a, LibV E W m0 a → ¬ fp a) : LibK E W m0 m2 := by
  refine ⟨h.1.trans (hk.mono fun a ha => ⟨(h.libV ha).2.2.1, hF a ha, (h.libV ha).2.2.2⟩), fun a ha hp => ?_⟩
  rcases hpg a hp with h' | h' | h'
  · exact (h.libV ha).2.2.1 h'
  · rw [(h.libV ha).2.2.2] at h'; cases h'
  · exact hF a ha h'

theorem LibK.libRet {E : Env} {W : World} {m0 : Memory} {s t : PState} (h : LibK E W m0 s.m.memory)
    {fp : Nat → Prop} (hL : LibRet E W fp s t) (hF : ∀ a, LibV E W m0 a → ¬ fp a) :
    LibK E W m0 t.m.memory :=
  h.lib hL.2.2.2.1 (fun a hp => (hL.2.2.2.2.1 a hp).elim Or.inl fun h => Or.inr (Or.inl h)) hF

theorem LibK.freeRet {E : Env} {W : World} {m0 : Memory} {s t : PState} (h : LibK E W m0 s.m.memory)
    {fp : Nat → Prop} (hL : FreeRet E W fp s t) (hF : ∀ a, LibV E W m0 a → ¬ fp a) :
    LibK E W m0 t.m.memory :=
  h.lib hL.2.2.2.1 hL.2.2.2.2.1 hF

/-- **A call from `u`** (the return address pushed above `lo`) with a `LibRet` frame. -/
theorem LibK.call {E : Env} {W : World} {m0 : Memory} {u v : PState} {a ret : Word}
    (h : LibK E W m0 u.m.memory) (hlo : E.S.lo ≤ (u.m.core.read .rsp - 8#64).toNat) {fp : Nat → Prop}
    (hL : LibRet E W fp (callEntry u a ret) v) (hF : ∀ a, LibV E W m0 a → ¬ fp a) :
    LibK E W m0 v.m.memory :=
  (show LibK E W m0 (callEntry u a ret).m.memory by rw [callEntry_mem]; exact h.push hlo).libRet hL hF

/-- A call with no footprint. -/
theorem LibK.call0 {E : Env} {W : World} {m0 : Memory} {u v : PState} {a ret : Word}
    (h : LibK E W m0 u.m.memory) (hlo : E.S.lo ≤ (u.m.core.read .rsp - 8#64).toNat)
    (hL : LibRet E W (fun _ => False) (callEntry u a ret) v) : LibK E W m0 v.m.memory :=
  h.call hlo hL fun _ _ h => h

/-- The footprint is private or unmapped in `m1` (`malloc`'s block, `fopen`'s stream): it holds
no library variable of `m0`. -/
theorem LibK.fresh {E : Env} {W : World} {m0 m1 : Memory} (h : LibK E W m0 m1) {a : Nat}
    (hf : E.S.priv m1 a ∨ m1.permits .read a = false) : ¬ LibV E W m0 a := fun ha => by
  rcases hf with hf | hf
  · exact (h.libV ha).2.2.1 hf
  · rw [(h.libV ha).2.2.2] at hf; cases hf

/-- Addresses at or above `lo` are no library variables. -/
theorem LibV.lo {E : Env} {W : World} {m0 : Memory} {a : Nat} (ha : LibV E W m0 a) : a < E.S.lo := ha.1

end Silmaril.Elf.Link.Dyn.Sha256sum
