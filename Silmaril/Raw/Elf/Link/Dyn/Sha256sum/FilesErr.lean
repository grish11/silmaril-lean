module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.FilesOpen

/-! # GNU `sha256sum`: `digest_file` on a file that cannot be opened (proof)

`sha_digest_err` follows `digest_file` from `*missing = false` (`DigMid`, `0x6a88`) through
`fopen_safer` (`sha_fopenSaferNull`), the `ignore_missing` test, `quotef` (`Task.quotef`),
`__errno_location` and `error (0, errno, "%s", …)` to the return (`dg_epiR`);
`task_digestOpenErr` adds the prologue (`sha_digest_pro`, `sha_digest_mid`).

`LK s m`: the memory `NPo` of `s` (library variables below the streams, the caller's stack) is
as in `s` and still non-private; `LK.lib` carries it across a library call, `LK.prog` across the
program's own stores.
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

/-- `cmp byte [rip + d], 0`. -/
theorem exec_cmpb0_rip (d : BitVec 32) (c : State) (m : Memory) (l : Nat) (v : Word)
    (h : loadN m (c.rip + BitVec.ofNat 64 l + d.signExtend 64) 1 = some v) :
    Silmaril.X86.Ext9.exec (.ext8 (.base (.cmpI8 (.mem (Silmaril.X86.Ext.Mem.ofRip d)) 0#8))) c m l =
      .ok { c with flags := Silmaril.X86.Ext.subFlagsN (v.setWidth 8) 0#8, rip := c.rip + BitVec.ofNat 64 l } m := by
  simp [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire,
    Silmaril.X86.Ext.readNarrow, Silmaril.X86.Ext.Narrow.bytes, Silmaril.X86.Ext.Narrow.bits,
    Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Mem.ofRip, Silmaril.X86.Ext.Base.value, h]

/-- `mov dst32, dword [base]`. -/
theorem exec_loadd (dst base : Reg) (c : State) (m : Memory) (l : Nat) (v : Word)
    (h : loadN m (c.read base) 4 = some v) :
    Silmaril.X86.Ext9.exec (.ext8 (.base (.load .d dst (Silmaril.X86.Ext.Mem.ofReg base Option.none 0#32)))) c m l =
      .ok { c.write dst ((v.setWidth 32).setWidth 64) with rip := c.rip + BitVec.ofNat 64 l } m := by
  simp [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire,
    Silmaril.X86.Ext.readRM, h, Silmaril.X86.Ext.Sz.bytes, Silmaril.X86.Ext.Sz.write, ofReg_addr]

/-- The library memory of `s` (`NPo`) is kept up to `m` and still non-private. -/
def LK (E : Env) (b : Word) (s : PState) (m : Memory) : Prop :=
  Keeps (NPo E b s) s.m.memory m ∧ ∀ a, NPo E b s a → ¬ E.S.priv m a

theorem LK.lib {E : Env} {b : Word} {s : PState} {m1 m2 : Memory} (h : LK E b s m1) {F : Nat → Prop}
    (hk : Keeps (fun a => ¬ E.S.priv m1 a ∧ m1.permits .read a = true ∧ F a) m1 m2)
    (hpg : ∀ a, E.S.priv m2 a → E.S.priv m1 a ∨ m1.permits .read a = false)
    (hF : ∀ a, NPo E b s a → F a) : LK E b s m2 := by
  have hr : ∀ a, NPo E b s a → m1.permits .read a = true := fun a ha => by
    rw [(h.1 a ha).2]; exact ha.2.1
  refine ⟨h.1.trans (hk.mono fun a ha => ⟨h.2 a ha, hr a ha, hF a ha⟩), fun a ha hp => ?_⟩
  rcases hpg a hp with h' | h'
  · exact h.2 a ha h'
  · rw [hr a ha] at h'; cases h'

theorem LK.prog {E : Env} {b : Word} {s : PState} {m1 m2 : Memory} (h : LK E b s m1)
    (hk : Keeps (fun a => NPo E b s a ∨ E.S.priv m1 a) m1 m2) : LK E b s m2 := by
  have hp : E.S.priv m2 = E.S.priv m1 := E.S.priv_keep _ _ (hk.mono fun a ha => Or.inr ha)
  exact ⟨h.1.trans (hk.mono fun a ha => Or.inl ha), fun a ha => by rw [hp]; exact h.2 a ha⟩

/-- A push at `sp` below the caller's stack pointer and above the streams keeps `LK`. -/
theorem LK.push {E : Env} {b : Word} {s : PState} {m : Memory} (h : LK E b s m) {sp v : Word}
    (hlo : E.S.lo + 8 ≤ sp.toNat) (hhi : sp.toNat ≤ (s.m.core.read .rsp).toNat) :
    LK E b s (pushMem m sp v) := by
  have h8 : (sp - 8#64).toNat = sp.toNat - 8 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; simp
  refine h.prog (pushMem_keeps fun x hx => ?_)
  rw [h8]
  rcases hx with ⟨-, -, -, -, hx | hx⟩ | hx
  · omega
  · omega
  · have := E.S.priv_lo _ _ hx; omega

/-- `Appended` from an earlier state whose `stdout` and output were the call's. -/
theorem appended_pre {E : Env} {W : World} {s u t : PState}
    (hst : ∀ st, StdoutIs E s.m.memory st → StdoutIs E u.m.memory st) (ho : u.g.out = s.g.out)
    (h : Appended E W u t []) : Appended E W s t [] := by
  intro st hs
  obtain ⟨st', h1, h2, h3, h4⟩ := h st (hst st hs)
  exact ⟨st', h1, h2, h3, by rw [ho] at h4; exact h4⟩

/-- `Appended` to a later state with the same `stdout` and output. -/
theorem appended_post {E : Env} {W : World} {s t v : PState}
    (h : Appended E W s t []) (hst : ∀ st, StdoutIs E t.m.memory st → StdoutIs E v.m.memory st)
    (ho : v.g.out = t.g.out) : Appended E W s v [] := by
  intro st hs
  obtain ⟨st', h1, h2, h3, h4⟩ := h st hs
  exact ⟨st', hst st' h1, h2, h3, by rw [ho]; exact h4⟩

/-- A body with a stronger memory invariant and more written objects. -/
theorem _root_.Silmaril.Elf.Link.Dyn.Proc.BodyX.retarget {W : World} {M M' : Memory → Prop} {s u : PState} {fr n : Nat}
    {saved : List (Nat × Word)} {X X' : Nat → Prop} (h : BodyX W M s u fr n saved X) (hM : M' u.m.memory)
    (hX : ∀ a, X a → X' a) : BodyX W M' s u fr n saved X' :=
  ⟨h.rsp, h.keepX.mono fun a ha => ⟨ha.1, fun hx => ha.2 (hX a hx) |>.elim⟩, h.room, hM, h.fs, h.done,
    h.saved, h.perm⟩

theorem QSlots.keep {b : Word} (hb : b.toNat + 0xa188 < 2 ^ 64) {m m' : Memory} (h : QSlots b m)
    (hk : Keeps (ImgQ b) m m') : QSlots b m' := by
  have hl : ∀ {off n : Nat}, off + n ≤ 0xa060 → loadN m' (b + BitVec.ofNat 64 off) n =
      loadN m (b + BitVec.ofNat 64 off) n := by
    intro off n ho
    simp only [loadN, Memory.readBytes]
    rw [skeeps_range hb hk (by omega) (fun k hk => ⟨⟨by omega, by omega⟩, by unfold Slot0; omega⟩)]
  exact ⟨(hl (off := 0xa010) (by decide)).trans h.nslots, (hl (off := 0xa020) (by decide)).trans h.size,
    (hl (off := 0xa028) (by decide)).trans h.val, (hl (off := 0xa030) (by decide)).trans h.vec⟩

theorem ShaRO.keep {b lb : Word} {m m' : Memory} (h : ShaRO b lb m)
    (hk : Keeps (fun a => b.toNat + 0x2000 ≤ a ∧ a < b.toNat + 0xa000) m m') : ShaRO b lb m' := by
  obtain ⟨Fk, Fc, Fl, kb, ldb, res, ifn, m0, h1, h2, h3, h4, h5⟩ := h
  exact ⟨Fk, Fc, Fl, kb, ldb, res, ifn, m0, h1, h2, h3, h4, h5.trans hk⟩

theorem QImps.keep {E : Env} {W : World} {b lb : Word} {m m' : Memory} (h : QImps E W b lb m)
    (hk : Keeps (ImgQ b) m m') : QImps E W b lb m' := by
  obtain ⟨a, ha, hi⟩ := h.memcmp
  refine ⟨h.lz, h.img, h.hb, h.errno, h.mbcur, a, ?_, hi⟩
  rw [← ha]; simp only [loadN, Memory.readBytes]
  rw [skeeps_range (off := 0x9e18) h.hb hk (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, by unfold Slot0; omega⟩)]

theorem ErrnoIs.keep {E : Env} {m m' : Memory} {e : Silmaril.Apps.Sha256sum.Errno} (h : ErrnoIs E m e)
    (hk : Keeps (fun a => E.errnoA.toNat ≤ a ∧ a < E.errnoA.toNat + 4) m m') : ErrnoIs E m' e := by
  exact ⟨by rw [hk.loadN (fun j hj => ⟨by omega, by omega⟩)]; exact h.1,
    (hk.permitted (fun j hj => ⟨by omega, by omega⟩)).2 h.2⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`digest_file` on a refused name, from `*missing = false`.** -/
theorem sha_digest_err {E : Env} {R : ShaRep} {W : World} {b lb kb pinA : Word} (I : DigImps E R W b lb kb)
    (K : ErrImps E W lb pinA) {Q : PState → Prop} {s x : PState} {p : List Byte}
    (hQ : ∀ s', QEntry E W b lb s' p → (∀ t, QExit E W b s' t p → MustQ W Q t) → MustQ W Q s')
    {e : Silmaril.Apps.Sha256sum.Errno} {g : Word} {prog : List Byte}
    (hE : DigEntryE E W b lb kb pinA s p e g prog) (hM : DigMid E W b lb kb s x g)
    (hrx : x.m.core.rip = b + 0x6a88#64) (h14x : BitVec.setWidth 32 (x.m.core.read .r14) ≠ 0#32)
    (k : ∀ t, DigErrExit E W b s t p e prog → MustQ W Q t) : MustQ W Q x := by
  have hin : ∀ n, n < 0xa188 → W.InImage (b + BitVec.ofNat 64 n).toNat := fun n hn => sha_in' I.cl.img I.cl.hb hn
  have hX := hE.outs
  have hp := hE.name
  have hpk : ∀ j, j < p.length + 1 → W.Kept ((s.m.core.read .rdi).toNat + j) := fun j hj => (hE.namek j hj).1
  have hlo8 := hE.lo
  have hNK : ∀ a, (s.m.core.read .rsp).toNat - 3072 ≤ a → a < (s.m.core.read .rsp).toNat + 8 → ¬ W.Kept a :=
    fun a h1 h2 => (hE.room.2.2 a h1 h2).2.2
  have hB := hM.body
  have hroom := hB.room
  have hsp := hroom.1
  have hsp2 := hroom.2.1
  have hMk := shaMemCD_keep (lb := lb) (kb := kb) I.cl.img I.cl.hb
  have e8 : (s.m.core.read .rsp - 8#64).toNat = (s.m.core.read .rsp).toNat - 8 :=
    sub_toNat (k := 8) (by omega) (by decide)
  have hne : Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.logicFlagsN
      (andD (BitVec.setWidth 32 (x.m.core.read .r14)) (BitVec.setWidth 32 (x.m.core.read .r14)))) .ne = some true := by
    rw [eval_ne_testD]; simp [h14x]
  refine must_listed (o := 72) shaD_listing_ok.2.2 rfl hB.done (by rw [hrx]; exact hin _ (by decide))
    hB.mem.2.digestFile (by rw [hrx, ripadd]) ?_
  xstep [hrx]
  refine must_listed (o := 75) shaD_listing_ok.2.2 rfl hB.done (hin _ (by decide)) hB.mem.2.digestFile (by rw [ripadd]) ?_
  xstep [hne]
  have hs1 : (x.m.core.read .rbp + BitVec.signExtend 64 0xffffff38#32).toNat = (s.m.core.read .rsp).toNat - 208 := by
    rw [hM.rbp, show BitVec.signExtend 64 0xffffff38#32 = 0xffffffffffffff38#64 by decide, BitVec.toNat_add, e8]
    simp only [BitVec.toNat_ofNat]; omega
  refine must_listed (o := 336) shaD_listing_ok.2.2 rfl hB.done (hin _ (by decide)) hB.mem.2.digestFile (by rw [ripadd]) ?_
  rw [exec_loadqd _ _ _ _ _ _ _ (by
    show loadN x.m.memory (x.m.core.read .rbp + BitVec.signExtend 64 0xffffff38#32) 8 = some (s.m.core.read .rdi)
    exact loadN_of_enc (by rw [hs1]; exact hM.slot1)), WP_ok]
  refine must_listed (o := 343) shaD_listing_ok.2.2 rfl hB.done (by simp only [ripadd]; exact hin _ (by decide))
    hB.mem.2.digestFile (by simp only [ripadd]) ?_
  xstep []
  -- fopen_safer (name, "r")
  have hxr : (x.m.core.read .rsp).toNat = (s.m.core.read .rsp).toNat - 216 := by
    rw [hB.rsp]; exact sub_toNat (by omega) (by decide)
  have hx8 : (x.m.core.read .rsp - 8#64).toNat = (s.m.core.read .rsp).toNat - 224 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), hxr]; omega
  have pw : x.m.memory.Permitted .write (x.m.core.read .rsp - 8#64).toNat 8 :=
    room_perm hroom (Or.inr rfl) (by omega) (by omega)
  have pr : x.m.memory.Permitted .read (x.m.core.read .rsp - 8#64).toNat 8 :=
    room_perm hroom (Or.inl rfl) (by omega) (by omega)
  have hpush : Keeps (fun a => W.Kept a ∨ (s.m.core.read .rsp).toNat - 216 ≤ a) x.m.memory
      (pushMem x.m.memory (x.m.core.read .rsp) (b + 27555#64)) := by
    refine pushMem_keeps fun a ha => ?_
    rw [hx8]
    rcases ha with ha | ha
    · by_contra hc
      exact (hroom.2.2 a (by omega) (by omega)).2.2 ha
    · omega
  have hKs : Keeps W.Kept s.m.memory (pushMem x.m.memory (x.m.core.read .rsp) (b + 27555#64)) :=
    (hB.keepX.mono fun a ha => ⟨Or.inl ha, fun hd => (hX a (Or.inl hd)).1 ha⟩).trans (hpush.mono fun a ha => Or.inl ha)
  have hp1 : CStr (pushMem x.m.memory (x.m.core.read .rsp) (b + 27555#64)) (s.m.core.read .rdi) p :=
    ⟨hp.1, by rw [hKs.readBytes (fun j hj => hpk j hj)]; exact hp.2⟩
  have hroom1 : Room W (pushMem x.m.memory (x.m.core.read .rsp) (b + 27555#64)) (x.m.core.read .rsp - 8#64) 256 := by
    rw [show x.m.core.read .rsp - 8#64 = s.m.core.read .rsp - BitVec.ofNat 64 224 by rw [hB.rsp]; bv_omega]
    exact (hroom.pushMem.down (d := 224) (by decide) (by decide)).mono (by decide)
  refine must_listed (o := 350) shaD_listing_ok.2.2 rfl hB.done (hin _ (by decide)) hB.mem.2.digestFile (by rw [ripadd]) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa using pw)]
  xstep []

  -- the library memory, up to the call
  have hLKx : LK E b s x.m.memory := by
    have hpx : E.S.priv x.m.memory = E.S.priv s.m.memory := E.S.priv_local _ _ hM.low
    refine ⟨fun a ha => ?_, fun a ha => by rw [hpx]; exact ha.1⟩
    rcases ha.2.2.2.2 with h | h
    · exact hM.low a h
    · exact hB.keepX a ⟨Or.inr h, fun hm => ha.2.2.2.1 (Or.inl hm)⟩
  have hLK1 : LK E b s (pushMem x.m.memory (x.m.core.read .rsp) (b + 27555#64)) :=
    hLKx.push (by rw [hxr]; omega) (by rw [hxr]; omega)
  refine sha_fopenSaferNull I.cl I.fopen (p := p) (e := e) rfl
    (abiEntry_of (v := b + 27555#64) (by show (x.m.core.read .rsp - 8#64).toNat % 16 = 8; rw [hx8]; have := hE.abi.aligned; omega)
      (by simpa using pushMem_read pr pw))
    (by simpa using hroom1) (by show E.S.lo + 256 ≤ (x.m.core.read .rsp - 8#64).toNat; rw [hx8]; omega) hB.done
    (hMk _ _ hB.mem (hpush.mono fun a ha => Or.inl (Or.inl ha))) (by simpa using hp1) (by simpa using hpk) hE.file ?_
  intro t habiT hkT hgT hraxT herrT hokT hfsT hPT hnpT hprT
  obtain ⟨hB1, hrip1, hrsp1, hcs1⟩ := body_after (shaMemCD_keep I.cl.img I.cl.hb) hB (by decide) (by decide)
    (sv6_bound s) (ret := b + 27555#64)
    (hpost := ⟨⟨habiT, hkT.mono fun a ha => ha.1⟩, halfOfKeep hkT hPT, by rw [hgT]; exact hB.done⟩)
    (hem := by exact rfl) (hersp := by simp)
    (hecs := by
      intro r hr
      simp only [Silmaril.X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
    (hefs := by exact rfl) (hvfs := hfsT) (hfp := fun x (h : False) => h.elim) (hX := fun x hd => Or.inr (hX x (Or.inl hd)).2)
  have hkF : Keeps (fun a => (s.m.core.read .rsp).toNat - 216 ≤ a ∧ a < (s.m.core.read .rsp).toNat) x.m.memory t.m.memory :=
    (hpush.mono fun a ha => Or.inr ha.1).trans (hkT.mono fun a ha => Or.inr (by
      show (x.m.core.read .rsp - 8#64).toNat ≤ a; rw [hx8]; omega))
  have hFx : ∀ f st', E.S.file s.m.memory f st' → E.S.file x.m.memory f st' := fun f st' h =>
    (E.S.local_ _ _ _ _ (fun a ha => hM.low a (E.S.foot_lo _ _ _ _ h ha)) h).1
  have hFt : ∀ f st', E.S.file s.m.memory f st' → E.S.file t.m.memory f st' := fun f st' h =>
    hokT f st' (by simpa using file_push (v := b + 27555#64) (hFx f st' h) (by rw [hx8]; omega))
  have hgt : t.g = s.g := by rw [hgT]; simp only; exact hM.g
  have hcs : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, t.m.core.read r = x.m.core.read r := hcs1
  have hLKt : LK E b s t.m.memory := by
    refine hLK1.lib (F := fun a => (x.m.core.read .rsp - 8#64).toNat ≤ a ∨ a + 256 < (x.m.core.read .rsp - 8#64).toNat)
      (by simpa using hnpT) (by simpa using hprT) ?_
    intro a ha
    rw [hx8]
    rcases ha.2.2.2.2 with h | h <;> omega
  -- image facts and the error path's memory invariant at `t`
  have hKt : Keeps (ShaImg b) s.m.memory t.m.memory := hB1.keepX.mono fun a ha =>
    ⟨Or.inl (Or.inl (by rw [I.cl.img]; exact ha)), fun hm => (hX a (Or.inl hm)).1 (Or.inl (by rw [I.cl.img]; exact ha))⟩
  have hMKt : ShaMemK b lb t.m.memory := hE.memK.keep I.cl.hb hKt
  have hza : Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.logicFlagsN (andQ (t.m.core.read .rax) (t.m.core.read .rax)))
      .e = some true := by rw [eval_e_testQ]; simp [hraxT]
  refine must_listed (o := 355) shaD_listing_ok.2.2 rfl hB1.done (by rw [hrip1]; exact hin _ (by decide))
    hB1.mem.2.digestFile (by rw [hrip1, ripadd]) ?_
  xstep [hrip1]
  refine must_listed (o := 358) shaD_listing_ok.2.2 rfl hB1.done (hin _ (by decide)) hB1.mem.2.digestFile (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 361) shaD_listing_ok.2.2 rfl hB1.done (hin _ (by decide)) hB1.mem.2.digestFile (by rw [ripadd]) ?_
  xstep [hza]
  refine must_gen (fun u => u.m.core.rip = b + 0x6cce#64 ∧ u.m.memory = t.m.memory ∧ u.g = t.g ∧
      u.m.core.read .rsp = t.m.core.read .rsp ∧ u.m.core.fsBase = t.m.core.fsBase ∧
      (∀ r ∈ Silmaril.X86.sysv64.calleeSaved, r ≠ .rbx → u.m.core.read r = t.m.core.read r)) ?_ ?_
  · refine ⟨rfl, rfl, rfl, by simp, rfl, fun r hr hne => ?_⟩
    simp only [Silmaril.X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact absurd rfl hne | simp
  rintro u ⟨hru, hmu, hgu, hspu, hfsu, hcsu⟩
  have hBu : BodyX W (ShaMemCD b lb kb) s u 216 1024 (sv6 s) (MX s) := hB1.of_eq hmu hspu hfsu (by rw [hgu])
  -- `ignore_missing` is false: on to `error`
  have hig : loadN u.m.memory (u.m.core.rip + BitVec.ofNat 64 7 + BitVec.signExtend 64 0x349c#32) 1 = some 0#64 := by
    rw [hru, hmu, show b + 0x6cce#64 + BitVec.ofNat 64 7 + BitVec.signExtend 64 0x349c#32 = b + 0xa171#64 by
      simp only [BitVec.add_assoc]; rfl]
    simpa using loadN_one hMKt.ignore
  refine must_listed (o := 654) shaD_listing_ok.2.2 rfl hBu.done (by rw [hru]; exact hin _ (by decide))
    hBu.mem.2.digestFile (by rw [hru, ripadd]) ?_
  rw [exec_cmpb0_rip _ _ _ _ _ hig, WP_ok]
  have hje : Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.subFlagsN ((0#64 : Word).setWidth 8) 0#8) .e = some true := by
    decide
  refine must_listed (o := 661) shaD_listing_ok.2.2 rfl hBu.done (by simp only [hru, ripadd]; exact hin _ (by decide))
    hBu.mem.2.digestFile (by simp only [hru, ripadd]) ?_
  xstep [hru, hje]
  refine must_gen (fun v => v.m.core.rip = b + 0x6ceb#64 ∧ v.m.memory = t.m.memory ∧ v.g = t.g ∧
      v.m.core.read .rsp = t.m.core.read .rsp ∧ v.m.core.fsBase = t.m.core.fsBase ∧
      (∀ r ∈ Silmaril.X86.sysv64.calleeSaved, r ≠ .rbx → v.m.core.read r = t.m.core.read r)) ?_ ?_
  · refine ⟨rfl, hmu, hgu, by simp [hspu], by simp [hfsu], fun r hr hne => ?_⟩
    simp only [st_read_mk]
    exact hcsu r hr hne
  clear hBu hig hje
  rintro u ⟨hru, hmu, hgu, hspu, hfsu, hcsu⟩
  have hBu : BodyX W (ShaMemCD b lb kb) s u 216 1024 (sv6 s) (MX s) := hB1.of_eq hmu hspu hfsu (by rw [hgu])
  have hrbpu : u.m.core.read .rbp = s.m.core.read .rsp - 8#64 := by
    rw [hcsu .rbp (by simp [Silmaril.X86.sysv64_calleeSaved]) (by decide),
      hcs .rbp (by simp [Silmaril.X86.sysv64_calleeSaved])]; exact hM.rbp
  have hs1u : (u.m.core.read .rbp + BitVec.signExtend 64 0xffffff38#32).toNat = (s.m.core.read .rsp).toNat - 208 := by
    rw [hrbpu, show BitVec.signExtend 64 0xffffff38#32 = 0xffffffffffffff38#64 by decide, BitVec.toNat_add, e8]
    simp only [BitVec.toNat_ofNat]; omega
  have hslot1 : u.m.memory.readBytes ((s.m.core.read .rsp).toNat - 208) 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [s.m.core.read .rdi]) := by
    rw [hmu, hkF.readBytes (fun j hj => ⟨by omega, by omega⟩)]; exact hM.slot1
  refine must_listed (o := 683) shaD_listing_ok.2.2 rfl hBu.done (by rw [hru]; exact hin _ (by decide))
    hBu.mem.2.digestFile (by rw [hru, ripadd]) ?_
  rw [exec_loadqd _ _ _ _ _ _ _ (by
    show loadN u.m.memory (u.m.core.read .rbp + BitVec.signExtend 64 0xffffff38#32) 8 = some (s.m.core.read .rdi)
    exact loadN_of_enc (by rw [hs1u]; exact hslot1)), WP_ok]
  -- the call of `quotef`
  have hur : (u.m.core.read .rsp).toNat = (s.m.core.read .rsp).toNat - 216 := by
    rw [hBu.rsp]; exact sub_toNat (by omega) (by decide)
  have hu8 : (u.m.core.read .rsp - 8#64).toNat = (s.m.core.read .rsp).toNat - 224 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), hur]; omega
  have pwu : u.m.memory.Permitted .write (u.m.core.read .rsp - 8#64).toNat 8 :=
    room_perm hBu.room (Or.inr rfl) (by omega) (by omega)
  have pru : u.m.memory.Permitted .read (u.m.core.read .rsp - 8#64).toNat 8 :=
    room_perm hBu.room (Or.inl rfl) (by omega) (by omega)
  refine must_listed (o := 690) shaD_listing_ok.2.2 rfl hBu.done (by simp only [hru, ripadd]; exact hin _ (by decide))
    hBu.mem.2.digestFile (by simp only [hru, ripadd]) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa using pwu)]
  xstep [hru]
  refine must_gen (fun e2 => e2.m.core.rip = b + 0x6950#64 ∧
      e2.m.memory = pushMem u.m.memory (u.m.core.read .rsp) (b + 27895#64) ∧
      e2.m.core.read .rsp = u.m.core.read .rsp - 8#64 ∧ e2.m.core.read .rdi = s.m.core.read .rdi ∧ e2.g = u.g ∧
      e2.m.core.fsBase = u.m.core.fsBase ∧
      (∀ r ∈ Silmaril.X86.sysv64.calleeSaved, e2.m.core.read r = u.m.core.read r)) ?_ ?_
  · refine ⟨by bv_omega, rfl, by simp, by simp, rfl, rfl, fun r hr => ?_⟩
    have h1 : r ≠ .rsp := by rintro rfl; simp [Silmaril.X86.sysv64_calleeSaved] at hr
    have h2 : r ≠ .rdi := by rintro rfl; simp [Silmaril.X86.sysv64_calleeSaved] at hr
    simp [h1, h2]
  rintro e2 ⟨hre2, hme2, hspe2, hrdie2, hge2, hfse2, hcse2⟩
  have he2r : (e2.m.core.read .rsp).toNat = (s.m.core.read .rsp).toNat - 224 := by rw [hspe2, hu8]
  -- what `quotef` needs
  have hKu : Keeps (fun a => (W.Kept a ∨ (s.m.core.read .rsp).toNat ≤ a) ∧ ¬ MX s a) s.m.memory e2.m.memory := by
    rw [hme2]
    exact hBu.keepX.trans (pushMem_keeps fun a ha => by
      rw [hu8]
      rcases ha.1 with h | h
      · by_cases hc : (s.m.core.read .rsp).toNat - 3072 ≤ a ∧ a < (s.m.core.read .rsp).toNat + 8
        · exact absurd h (hNK a hc.1 hc.2)
        · omega
      · omega)
  have hKimg : Keeps (ImgQ b) s.m.memory e2.m.memory := hKu.mono fun a ha =>
    ⟨Or.inl (Or.inl (by rw [I.cl.img]; exact ha.1)), fun hm => (hX a (Or.inl hm)).1 (Or.inl (by rw [I.cl.img]; exact ha.1))⟩
  have hslot0 : ∀ a, Slot0 b a → e2.m.memory.permits .read a = true ∧ e2.m.memory.permits .write a = true ∧
      ¬ E.S.priv e2.m.memory a := by
    intro a ha
    have hka : W.Kept a := Or.inl (by rw [I.cl.img]; unfold Slot0 at ha; unfold ShaImg; omega)
    have hk := hKu a ⟨Or.inl hka, fun hm => (hX a (Or.inl hm)).1 hka⟩
    have hkx := hB.keepX a ⟨Or.inl hka, fun hm => (hX a (Or.inl hm)).1 hka⟩
    obtain ⟨h1, h2, h3⟩ := hE.slot0 a ha
    refine ⟨by rw [hk.2]; exact h1, by rw [hk.2]; exact h2, fun hp => ?_⟩
    have hpx : E.S.priv x.m.memory = E.S.priv s.m.memory := E.S.priv_local _ _ hM.low
    have hp1 : E.S.priv (pushMem x.m.memory (x.m.core.read .rsp) (b + 27555#64)) = E.S.priv x.m.memory :=
      E.S.priv_keep _ _ (pushMem_keeps fun y hy => by rw [hx8]; have := E.S.priv_lo _ _ hy; omega)
    have hp2 : E.S.priv e2.m.memory = E.S.priv t.m.memory := by
      rw [hme2, hmu]
      exact E.S.priv_keep _ _ (pushMem_keeps fun y hy => by rw [hu8]; have := E.S.priv_lo _ _ hy; omega)
    rw [hp2] at hp
    rcases hprT a hp with h | h
    · rw [hp1, hpx] at h; exact h3 h
    · rw [pushMem_permits, hkx.2] at h; rw [h1] at h; cases h
  refine hQ e2 ⟨hre2, abiEntry_of (v := b + 27895#64) (by rw [he2r]; have := hE.abi.aligned; omega)
      (by rw [hme2, hspe2]; exact pushMem_read pru pwu), by rw [hge2]; exact hBu.done,
    hE.qimps.keep hKimg, ?_, by rw [he2r]; omega, hE.ro.keep (hKimg.mono fun a ha => ⟨⟨by omega, by omega⟩,
      by unfold Slot0; omega⟩), hE.slots.keep I.cl.hb hKimg, hslot0, ?_, ?_, hE.fits, ?_, ?_, ?_, ?_, ?_⟩ ?_
  · have hR : Room W e2.m.memory (s.m.core.read .rsp) 3072 := hE.room.keeps fun a h1 h2 acc => by
      rw [hme2, pushMem_permits, hBu.perm a (by omega) h2 acc]
    rw [show e2.m.core.read .rsp = s.m.core.read .rsp - BitVec.ofNat 64 224 by rw [hspe2, hBu.rsp]; bv_omega]
    exact (hR.down (by decide) (by decide)).mono (by decide)
  · rw [hrdie2]; exact ⟨hp.1, by rw [hKu.readBytes (fun j hj => ⟨Or.inl (hpk j hj), fun hm =>
      (hX _ (Or.inl hm)).1 (hpk j hj)⟩)]; exact hp.2⟩
  · rw [hrdie2]; exact hE.namek
  · refine ⟨g, ?_⟩
    rw [hfse2, hBu.fs, hKu.loadN (fun j hj => ⟨Or.inl (hE.guardk j hj), fun hm => (hX _ (Or.inl hm)).1 (hE.guardk j hj)⟩)]
    exact hE.guard
  · rw [hfse2, hBu.fs]; exact hE.guardk
  · rw [hfse2, hBu.fs]; exact hE.guardq
  · exact hE.errnoLo
  · have h : ErrnoIs E e2.m.memory e := by
      rw [hme2, hmu]; exact ErrnoIs.keep herrT (pushMem_keeps fun y hy => by rw [hu8]; have := hE.errnoLo; omega)
    exact ⟨_, h.1⟩
  intro t2 hQX
  -- back in `digest_file` (`0x6cf7`), with `slot0` among the objects it has written
  have hal : (s.m.core.read .rsp).toNat % 16 = 8 := hE.abi.aligned
  have hX2 : ∀ a, MX s a ∨ Slot0 b a → a + 1024 < (s.m.core.read .rsp).toNat ∨ (s.m.core.read .rsp).toNat + 8 ≤ a := by
    rintro a (hm | hs)
    · exact Or.inr (hX a (Or.inl hm)).2
    · have hka : W.Kept a := Or.inl (by rw [I.cl.img]; unfold Slot0 at hs; unfold ShaImg; omega)
      by_contra hc
      exact hNK a (by omega) (by omega) hka
  have hBu2 : BodyX W (fun m => ShaMemCD b lb kb m ∧ ShaMemK b lb m) s u 216 1024 (sv6 s)
      (fun a => MX s a ∨ Slot0 b a) :=
    hBu.retarget ⟨hBu.mem, by rw [hmu]; exact hMKt⟩ fun a ha => Or.inl ha
  have hQimg : ∀ m m' : Memory, Keeps (fun y => W.InImage y ∧ ¬ QW b e2 y) m m' → Keeps (ImgQ b) m m' :=
    fun m m' hk => hk.mono fun y hy => ⟨by rw [I.cl.img]; exact hy.1, by
      rintro (h | ⟨h1, h2⟩)
      · exact hy.2 h
      · exact hNK y (by rw [he2r] at h1; omega) (by rw [he2r] at h2; omega) (Or.inl (by rw [I.cl.img]; exact hy.1))⟩
  obtain ⟨hB2, hrip2, hrsp2, hcs2⟩ := body_afterK (fp := QW b e2)
    (fun m m' hm hk => ⟨⟨hm.1.1.keepQ I.cl.hb (hQimg m m' hk), hm.1.2.keepQ I.cl.hb (hQimg m m' hk)⟩,
      hm.2.keepQ I.cl.hb (hQimg m m' hk)⟩)
    hBu2 (by decide) (by decide) (sv6_bound s) (ret := b + 27895#64)
    (hem := hme2) (hersp := hspe2) (hecs := hcse2) (hefs := hfse2)
    (hpost := ⟨hQX.ret.1, halfOfStack hQX.ret.2.2.1, by rw [hQX.g, hge2]; exact hBu.done⟩)
    (hvfs := hQX.ret.2.1)
    (hfp := by
      rintro y (h | ⟨h1, h2⟩)
      · exact Or.inl (Or.inr h)
      · right
        rw [he2r] at h1 h2
        exact ⟨hNK y (by omega) (by omega), by omega⟩)
    (hX := hX2)
  have ht2r : (t2.m.core.read .rsp).toNat = (s.m.core.read .rsp).toNat - 216 := by rw [hrsp2, hur]
  have herrE : ErrnoIs E e2.m.memory e := by
    rw [hme2, hmu]; exact ErrnoIs.keep herrT (pushMem_keeps fun y hy => by rw [hu8]; have := hE.errnoLo; omega)
  have herr2 : ErrnoIs E t2.m.memory e := hQX.errno e herrE
  have hMimg : ∀ m m' : Memory, ShaMemCD b lb kb m ∧ ShaMemK b lb m → Keeps W.InImage m m' →
      ShaMemCD b lb kb m' ∧ ShaMemK b lb m' := fun m m' hm hk =>
    ⟨shaMemCD_keep I.cl.img I.cl.hb m m' hm.1 hk, hm.2.keep I.cl.hb (by rw [I.cl.img] at hk; exact hk)⟩
  -- `mov rbx, rax` (the quoted name), `call __errno_location`
  refine must_listed (o := 695) shaD_listing_ok.2.2 rfl hB2.done (by rw [hrip2]; exact hin _ (by decide))
    hB2.mem.1.2.digestFile (by rw [hrip2, ripadd]) ?_
  xstep [hrip2]
  refine must_gen (fun w2 => w2.m.core.rip = b + 0x6cfa#64 ∧ w2.m.memory = t2.m.memory ∧ w2.g = t2.g ∧
      w2.m.core.read .rsp = t2.m.core.read .rsp ∧ w2.m.core.fsBase = t2.m.core.fsBase ∧
      w2.m.core.read .rbx = t2.m.core.read .rax ∧
      (∀ r ∈ Silmaril.X86.sysv64.calleeSaved, r ≠ .rbx → w2.m.core.read r = t2.m.core.read r)) ?_ ?_
  · refine ⟨rfl, rfl, rfl, by simp, rfl, by simp, fun r hr hne => ?_⟩
    simp only [Silmaril.X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact absurd rfl hne | simp
  rintro w2 ⟨hrw2, hmw2, hgw2, hspw2, hfsw2, hbxw2, hcsw2⟩
  refine body_call hMimg (hB2.of_eq hmw2 hspw2 hfsw2 (by rw [hgw2])) (by decide) (by decide) (sv6_bound s) (by omega) I.cl.lz
    (o := 698) (so := 0x20) (pb := b + 0x23c0#64) (fp := fun _ => False)
    shaD_listing_ok.2.2 rfl (by rw [hrw2]; exact hin _ (by decide)) (fun m h => h.1.2.digestFile)
    (by rw [hrw2, ripadd]) shaC_listing_ok.1 rfl rfl (by simp only [BitVec.add_assoc]; rfl)
    (img_off I.cl.img I.cl.hb (by decide)) (img_off I.cl.img I.cl.hb (by decide)) (fun m h => h.1.1.plt)
    (fun m h => by
      rw [show b + 0x23c0#64 + BitVec.ofNat 64 (0x20 + 4 + 6) + BitVec.signExtend 64 0x79fe#32 = b + 0x9de8#64 by
        simp only [BitVec.add_assoc]; rfl]
      exact h.2.errnoG)
    K.errno.1 K.errno.2.1 K.errno.2.2.1 (fun r h => (impOk_fn K.errno _ r).1 h)
    (fun he => he)
    (fun v hv => ⟨hv.1.1, hv.1.2.2.1, by simpa [callEntry] using hv.1.2.1, by rw [hv.2.1, callEntry_g, hgw2]; exact hB2.done⟩)
    (fun y h => h.elim) hX2 ?_
  intro v3 hv3 hB3 hrip3 hrsp3 hcs3
  obtain ⟨hlib3, hg3, hok3, hrax3, herr3, -, -⟩ := hv3
  -- what is kept up to `v3`
  have hLKe2 : LK E b s e2.m.memory := by
    rw [hme2, hmu]; exact hLKt.push (by rw [hur]; omega) (by rw [hur]; omega)
  have hQWnp : ∀ a, NPo E b s a → ¬ QW b e2 a := by
    rintro a ha (h | ⟨h1, h2⟩)
    · exact ha.2.2.1 h
    · rw [he2r] at h1 h2
      rcases ha.2.2.2.2 with h | h <;> omega
  have hLKt2 : LK E b s t2.m.memory :=
    hLKe2.lib (F := fun a => ¬ QW b e2 a) (hQX.ret.2.2.2.1.mono fun a ha => ⟨ha.1, ha.2.2, ha.2.1⟩)
      hQX.ret.2.2.2.2.1 hQWnp
  have hLKc3 : LK E b s (callEntry w2 (lb + 0x2a6e0#64) (b + 0x6a40#64 + BitVec.ofNat 64 (698 + 5))).m.memory := by
    rw [callEntry_mem, hmw2, hspw2]; exact hLKt2.push (by rw [ht2r]; omega) (by rw [ht2r]; omega)
  have hLKv3 : LK E b s v3.m.memory :=
    hLKc3.lib (F := fun _ => True) (hlib3.2.2.2.1.mono fun a ha => ⟨ha.1, fun h => h, ha.2.1⟩) hlib3.2.2.2.2.1
      (fun _ _ => trivial)
  have hw2r : (w2.m.core.read .rsp).toNat = (s.m.core.read .rsp).toNat - 216 := by rw [hspw2, ht2r]
  have hw28 : (w2.m.core.read .rsp - 8#64).toNat = (s.m.core.read .rsp).toNat - 224 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), hw2r]; omega
  have herrV3 : ErrnoIs E v3.m.memory e := herr3 e (by
    rw [callEntry_mem, hmw2]
    exact ErrnoIs.keep herr2 (pushMem_keeps fun y hy => by rw [hw28]; have := hE.errnoLo; omega))
  -- `mov rcx, rbx`, `lea rdx, "%s"`, `xor edi, edi`
  refine must_listed (o := 703) shaD_listing_ok.2.2 rfl hB3.done (by rw [hrip3]; exact img_off I.cl.img I.cl.hb (by decide))
    hB3.mem.1.2.digestFile (by rw [hrip3]) ?_
  xstep [hrip3]
  refine must_listed (o := 706) shaD_listing_ok.2.2 rfl hB3.done (hin _ (by decide)) hB3.mem.1.2.digestFile (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 713) shaD_listing_ok.2.2 rfl hB3.done (hin _ (by decide)) hB3.mem.1.2.digestFile (by rw [ripadd]) ?_
  xstep []
  refine must_gen (fun w4 => w4.m.core.rip = b + 0x6d0b#64 ∧ w4.m.memory = v3.m.memory ∧ w4.g = v3.g ∧
      w4.m.core.read .rsp = v3.m.core.read .rsp ∧ w4.m.core.fsBase = v3.m.core.fsBase ∧
      w4.m.core.read .rax = E.errnoA ∧ w4.m.core.read .rcx = t2.m.core.read .rax ∧
      w4.m.core.read .rdx = b + 0x70fa#64 ∧ low32 (w4.m.core.read .rdi) = 0#32 ∧
      (∀ r ∈ Silmaril.X86.sysv64.calleeSaved, w4.m.core.read r = v3.m.core.read r)) ?_ ?_
  · refine ⟨rfl, rfl, rfl, by simp, rfl, by simp [hrax3], ?_, ?_, by simp [low32, Silmaril.X86.Ext.AluOp.resultN], ?_⟩
    · simp only [st_read_mk]
      simp [hcs3 .rbx (by simp [Silmaril.X86.sysv64_calleeSaved]), hbxw2]
    · simp only [st_read_mk]
      simp only [Silmaril.Machine.RegisterFile.write_other, ne_eq, reduceCtorEq, not_false_eq_true,
        Silmaril.Machine.RegisterFile.write_same]
    · intro r hr
      simp only [Silmaril.X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  rintro w4 ⟨hrw4, hmw4, hgw4, hspw4, hfsw4, hraxw4, hrcxw4, hrdxw4, hrdiw4, hcsw4⟩
  have hBw4 : BodyX W (fun m => ShaMemCD b lb kb m ∧ ShaMemK b lb m) s w4 216 1024 (sv6 s)
      (fun a => MX s a ∨ Slot0 b a) := hB3.of_eq hmw4 hspw4 hfsw4 (by rw [hgw4])
  have hld : loadN w4.m.memory (w4.m.core.read .rax) 4 = some (BitVec.ofNat 64 (errnoCode e)) := by
    rw [hraxw4, hmw4]; exact herrV3.1
  refine must_listed (o := 715) shaD_listing_ok.2.2 rfl hBw4.done (by rw [hrw4]; exact hin _ (by decide))
    hBw4.mem.1.2.digestFile (by rw [hrw4, ripadd]) ?_
  rw [exec_loadd _ _ _ _ _ _ hld, WP_ok]
  refine must_listed (o := 717) shaD_listing_ok.2.2 rfl hBw4.done (by simp only [hrw4, ripadd]; exact hin _ (by decide))
    hBw4.mem.1.2.digestFile (by simp only [hrw4, ripadd]) ?_
  xstep [hrw4]
  refine must_gen (fun w5 => w5.m.core.rip = b + 0x6d0f#64 ∧ w5.m.memory = v3.m.memory ∧ w5.g = v3.g ∧
      w5.m.core.read .rsp = v3.m.core.read .rsp ∧ w5.m.core.fsBase = v3.m.core.fsBase ∧
      low32 (w5.m.core.read .rsi) = BitVec.ofNat 32 (errnoCode e) ∧ w5.m.core.read .rcx = t2.m.core.read .rax ∧
      w5.m.core.read .rdx = b + 0x70fa#64 ∧ low32 (w5.m.core.read .rdi) = 0#32 ∧
      (∀ r ∈ Silmaril.X86.sysv64.calleeSaved, w5.m.core.read r = v3.m.core.read r)) ?_ ?_
  · refine ⟨rfl, hmw4, hgw4, by simp [hspw4], by simp [hfsw4], ?_, by simp [hrcxw4], by simp [hrdxw4],
      by simp [low32] at hrdiw4 ⊢; exact hrdiw4, ?_⟩
    · simp [low32]
    · intro r hr
      have h0 := hcsw4 r hr
      simp only [Silmaril.X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simpa using h0
  rintro w5 ⟨hrw5, hmw5, hgw5, hspw5, hfsw5, hrsiw5, hrcxw5, hrdxw5, hrdiw5, hcsw5⟩
  have hBw5 : BodyX W (fun m => ShaMemCD b lb kb m ∧ ShaMemK b lb m) s w5 216 1024 (sv6 s)
      (fun a => MX s a ∨ Slot0 b a) := hB3.of_eq hmw5 hspw5 hfsw5 (by rw [hgw5])
  have hw5r : (w5.m.core.read .rsp).toNat = (s.m.core.read .rsp).toNat - 216 := by
    rw [hspw5, hrsp3, hw2r]
  have hw58 : (w5.m.core.read .rsp - 8#64).toNat = (s.m.core.read .rsp).toNat - 224 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), hw5r]; omega
  -- `error (0, errno, "%s", quotef (name))`: its precondition in the callee's entry memory
  have hKce : Keeps (fun a => (W.Kept a ∨ (s.m.core.read .rsp).toNat ≤ a) ∧ ¬ (MX s a ∨ Slot0 b a)) s.m.memory
      (pushMem w5.m.memory (w5.m.core.read .rsp) (b + 0x6a40#64 + BitVec.ofNat 64 (719 + 5))) :=
    hBw5.keepX.trans (pushMem_keeps fun a ha => by
      rw [hw58]
      rcases ha.1 with h | h
      · by_cases hc : (s.m.core.read .rsp).toNat - 3072 ≤ a ∧ a < (s.m.core.read .rsp).toNat + 8
        · exact absurd h (hNK a hc.1 hc.2)
        · omega
      · omega)
  have e70 : (b + 0x70fa#64).toNat = b.toNat + 0x70fa := addr_toNat (by have := I.cl.hb; omega)
  have hb60 : (b + 0xa060#64).toNat = b.toNat + 0xa060 := addr_toNat (by have := I.cl.hb; omega)
  have hslotK : ∀ a, Slot0 b a → W.Kept a := fun a ha =>
    Or.inl (by rw [I.cl.img]; unfold Slot0 at ha; unfold ShaImg; omega)
  have hpushImg : ∀ (m : Memory) (sp v : Word), (s.m.core.read .rsp).toNat - 1024 ≤ sp.toNat - 8 →
      sp.toNat ≤ (s.m.core.read .rsp).toNat → Keeps (fun a => W.Kept a) m (pushMem m sp v) := by
    intro m sp v h1 h2
    refine pushMem_keeps fun a ha => ?_
    have h8 : (sp - 8#64).toNat = sp.toNat - 8 := sub_toNat (k := 8) (by omega) (by decide)
    rw [h8]
    by_contra hc
    exact hNK a (by omega) (by omega) ha
  -- `slot0` from `t2` to `v3`: kept by `__errno_location` (non-private, mapped)
  have hS3 : ∀ a, Slot0 b a → (v3.m.memory.bytes.get? a = t2.m.memory.bytes.get? a ∧
      ∀ acc, v3.m.memory.permits acc a = t2.m.memory.permits acc a) ∧ ¬ E.S.priv v3.m.memory a := by
    intro a ha
    obtain ⟨hr2, -, hnp2⟩ := hQX.slot0 a ha
    have hk1 := hpushImg t2.m.memory (w2.m.core.read .rsp) (b + 0x6a40#64 + BitVec.ofNat 64 (698 + 5))
      (by rw [hw2r]; omega) (by rw [hw2r]; omega) a (hslotK a ha)
    have hpc : E.S.priv (pushMem t2.m.memory (w2.m.core.read .rsp) (b + 0x6a40#64 + BitVec.ofNat 64 (698 + 5))) =
        E.S.priv t2.m.memory :=
      E.S.priv_keep _ _ (pushMem_keeps fun y hy => by rw [hw28]; have := E.S.priv_lo _ _ hy; omega)
    have hnpc : ¬ E.S.priv (callEntry w2 (lb + 0x2a6e0#64) (b + 0x6a40#64 + BitVec.ofNat 64 (698 + 5))).m.memory a := by
      rw [callEntry_mem, hmw2, hpc]; exact hnp2
    have hrc : (callEntry w2 (lb + 0x2a6e0#64) (b + 0x6a40#64 + BitVec.ofNat 64 (698 + 5))).m.memory.permits .read a = true := by
      rw [callEntry_mem, hmw2, pushMem_permits]; exact hr2
    have hk2 := hlib3.2.2.2.1 a ⟨hnpc, fun h => h, hrc⟩
    rw [callEntry_mem, hmw2] at hk2
    refine ⟨⟨hk2.1.trans hk1.1, fun acc => (hk2.2 acc).trans (hk1.2 acc)⟩, fun hp => ?_⟩
    rcases hlib3.2.2.2.2.1 a hp with h | h
    · exact hnpc h
    · rw [hrc] at h; cases h
  -- the precondition of `error`
  obtain ⟨pa, hpa, hpstr⟩ := hE.progN
  set ret5 : Word := b + 0x6a40#64 + BitVec.ofNat 64 (719 + 5) with hret5
  set q := ofSpec (Silmaril.Apps.Sha256sum.quotef (toSpec p)) with hq
  have hqlen : q.length + 1 ≤ 256 := by
    have := hE.fits; simp only [hq, ofSpec, List.length_map]; omega
  have hpw5 : Keeps (fun a => W.Kept a) w5.m.memory (pushMem w5.m.memory (w5.m.core.read .rsp) ret5) :=
    hpushImg _ _ _ (by rw [hw5r]; omega) (by rw [hw5r]; omega)
  have hfmt : CStr (pushMem w5.m.memory (w5.m.core.read .rsp) ret5) (b + 0x70fa#64) fmtS := by
    refine ⟨by decide, ?_⟩
    have := I.cl.hb
    rw [hpw5.readBytes (fun j hj => Or.inl (by rw [I.cl.img, e70]; unfold ShaImg; simp [fmtS] at hj; omega))]
    exact hBw5.mem.2.fmtS
  have hqstr : CStr (pushMem w5.m.memory (w5.m.core.read .rsp) ret5) (b + 0xa060#64) q := by
    have hst := hQX.str
    refine ⟨hst.1, ?_⟩
    have hsl : ∀ j, j < q.length + 1 → Slot0 b ((b + 0xa060#64).toNat + j) := fun j hj => by
      rw [hb60]; unfold Slot0; omega
    rw [hpw5.readBytes (fun j hj => hslotK _ (hsl j hj)), hmw5]
    rw [show v3.m.memory.readBytes (b + 0xa060#64).toNat (q.length + 1) =
        t2.m.memory.readBytes (b + 0xa060#64).toNat (q.length + 1) from
      Keeps.readBytes (P := Slot0 b) (fun a ha => (hS3 a ha).1) hsl]
    exact hst.2
  have hprog5 : ProgName (pushMem w5.m.memory (w5.m.core.read .rsp) ret5) pinA prog := by
    refine ⟨pa, ?_, hpstr.1, ?_⟩
    · have hpin5 : Keeps (fun a => pinA.toNat ≤ a ∧ a < pinA.toNat + 8) s.m.memory
          (pushMem w5.m.memory (w5.m.core.read .rsp) ret5) := by
        refine (hLKv3.1.mono fun a ha => ?_).trans ?_
        · have := hE.pin (a - pinA.toNat) (by omega); rwa [show pinA.toNat + (a - pinA.toNat) = a by omega] at this
        · rw [hmw5]
          refine pushMem_keeps fun a ha => ?_
          rw [hw58]
          have := (hE.pin (a - pinA.toNat) (by omega)).2.2.2.2
          rw [show pinA.toNat + (a - pinA.toNat) = a by omega] at this
          rcases this with h | h <;> omega
      rw [hpin5.loadN (fun j hj => ⟨by omega, by omega⟩)]; exact hpa
    · rw [hKce.readBytes (fun j hj => ⟨Or.inl (hE.progk pa hpa j hj).1, by
        rintro (hm | hs)
        · exact (hX _ (Or.inl hm)).1 (hE.progk pa hpa j hj).1
        · exact (hE.progk pa hpa j hj).2 hs⟩)]
      exact hpstr.2
  -- `call error`
  refine body_call hMimg hBw5 (by decide) (by decide) (sv6_bound s) (by omega) I.cl.lz
    (o := 719) (so := 0x2d0) (pb := b + 0x23c0#64) (fp := fun _ => False)
    (post := fun v => LibRet E W (fun _ => False) (callEntry w5 (lb + 0x11e6c0#64) ret5) v ∧
      OthersKept E (callEntry w5 (lb + 0x11e6c0#64) ret5) v [E.stdoutF] ∧
      Appended E W (callEntry w5 (lb + 0x11e6c0#64) ret5) v [] ∧
      v.g = { (callEntry w5 (lb + 0x11e6c0#64) ret5).g with out := v.g.out, err := (callEntry w5 (lb + 0x11e6c0#64) ret5).g.err ++ errorMsg prog q e })
    shaD_listing_ok.2.2 rfl (by rw [hrw5]; exact hin _ (by decide)) (fun m h => h.1.2.digestFile)
    (by rw [hrw5, ripadd]) shaC_listing_ok.1 rfl rfl (by simp only [BitVec.add_assoc]; rfl)
    (img_off I.cl.img I.cl.hb (by decide)) (img_off I.cl.img I.cl.hb (by decide)) (fun m h => h.1.1.plt)
    (fun m h => by
      rw [show b + 0x23c0#64 + BitVec.ofNat 64 (0x2d0 + 4 + 6) + BitVec.signExtend 64 0x78a6#32 = b + 0x9f40#64 by
        simp only [BitVec.add_assoc]; rfl]
      exact h.2.errorG)
    K.error.1 K.error.2.1 K.error.2.2.1
    (fun r h hp => by
      obtain ⟨v, hv, hpost⟩ := (impOk_fn K.error _ r).1 h hp
      refine ⟨v, hv, ?_⟩
      have := hpost q prog e (by rw [callEntry_read _ _ _ (by decide), hrcxw5, hQX.rax]; exact hqstr)
        (by rw [callEntry_mem]; exact hprog5) (by rw [callEntry_read _ _ _ (by decide)]; exact hrsiw5)
      rw [callEntry_read _ _ _ (by decide), hrdiw5] at this
      simpa only [eq_self, ↓reduceIte] using this)
    (pre := AbiEntry (callEntry w5 (lb + 0x11e6c0#64) ret5).m.core (callEntry w5 (lb + 0x11e6c0#64) ret5).m.memory ∧
      CStr (callEntry w5 (lb + 0x11e6c0#64) ret5).m.memory ((callEntry w5 (lb + 0x11e6c0#64) ret5).m.core.read .rdx) fmtS ∧
      (∃ a, CStr (callEntry w5 (lb + 0x11e6c0#64) ret5).m.memory ((callEntry w5 (lb + 0x11e6c0#64) ret5).m.core.read .rcx) a) ∧
      (∃ prog, ProgName (callEntry w5 (lb + 0x11e6c0#64) ret5).m.memory pinA prog) ∧
      ∃ e, low32 ((callEntry w5 (lb + 0x11e6c0#64) ret5).m.core.read .rsi) = BitVec.ofNat 32 (errnoCode e))
    (fun habi => ⟨habi, by rw [callEntry_read _ _ _ (by decide), hrdxw5, callEntry_mem]; exact hfmt,
      ⟨q, by rw [callEntry_read _ _ _ (by decide), hrcxw5, hQX.rax, callEntry_mem]; exact hqstr⟩,
      ⟨prog, by rw [callEntry_mem]; exact hprog5⟩, ⟨e, by rw [callEntry_read _ _ _ (by decide)]; exact hrsiw5⟩⟩)
    (fun v hv => ⟨hv.1.1, hv.1.2.2.1, by simpa [callEntry] using hv.1.2.1, by
      rw [hv.2.2.2]; simp only [callEntry_g]; exact hBw5.done⟩)
    (fun y h => h.elim) hX2 ?_
  intro v5 hv5 hB5 hrip5 hrsp5 hcs5
  obtain ⟨hlib5, hok5, happ5, hg5⟩ := hv5
  -- `xor eax, eax`, `jmp 0x6b66`
  refine must_listed (o := 724) shaD_listing_ok.2.2 rfl hB5.done (by rw [hrip5]; exact img_off I.cl.img I.cl.hb (by decide))
    hB5.mem.1.2.digestFile (by rw [hrip5]) ?_
  xstep [hrip5]
  refine must_listed (o := 726) shaD_listing_ok.2.2 rfl hB5.done (hin _ (by decide)) hB5.mem.1.2.digestFile (by rw [ripadd]) ?_
  xstep []
  refine must_gen (fun w6 => w6.m.core.rip = b + 0x6b66#64 ∧ w6.m.memory = v5.m.memory ∧ w6.g = v5.g ∧
      w6.m.core.read .rsp = v5.m.core.read .rsp ∧ w6.m.core.fsBase = v5.m.core.fsBase ∧
      w6.m.core.read .rax = 0#64 ∧
      (∀ r ∈ Silmaril.X86.sysv64.calleeSaved, w6.m.core.read r = v5.m.core.read r)) ?_ ?_
  · refine ⟨rfl, rfl, rfl, by simp, rfl, by simp [Silmaril.X86.Ext.AluOp.resultN], ?_⟩
    intro r hr
    simp only [Silmaril.X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  rintro w6 ⟨hrw6, hmw6, hgw6, hspw6, hfsw6, hraxw6, hcsw6⟩
  -- the library state up to `v5`
  have hLKc5 : LK E b s (callEntry w5 (lb + 0x11e6c0#64) ret5).m.memory := by
    rw [callEntry_mem, hmw5]; exact hLKv3.push (by rw [hw5r]; omega) (by rw [hw5r]; omega)
  have hLKv5 : LK E b s v5.m.memory :=
    hLKc5.lib (F := fun _ => True) (hlib5.2.2.2.1.mono fun a ha => ⟨ha.1, fun h => h, ha.2.1⟩) hlib5.2.2.2.2.1
      (fun _ _ => trivial)
  -- `slot0` up to `v5`
  have hS5 : ∀ a, Slot0 b a → (v5.m.memory.bytes.get? a = v3.m.memory.bytes.get? a ∧
      ∀ acc, v5.m.memory.permits acc a = v3.m.memory.permits acc a) ∧ ¬ E.S.priv v5.m.memory a := by
    intro a ha
    have hk1 := hpw5 a (hslotK a ha)
    rw [hmw5] at hk1
    have hpc : E.S.priv (pushMem v3.m.memory (w5.m.core.read .rsp) ret5) = E.S.priv v3.m.memory :=
      E.S.priv_keep _ _ (pushMem_keeps fun y hy => by rw [hw58]; have := E.S.priv_lo _ _ hy; omega)
    have hnpc : ¬ E.S.priv (callEntry w5 (lb + 0x11e6c0#64) ret5).m.memory a := by
      rw [callEntry_mem, hmw5, hpc]; exact (hS3 a ha).2
    have hrc : (callEntry w5 (lb + 0x11e6c0#64) ret5).m.memory.permits .read a = true := by
      rw [callEntry_mem, hmw5, pushMem_permits, ((hS3 a ha).1.2 .read)]; exact (hQX.slot0 a ha).1
    have hk2 := hlib5.2.2.2.1 a ⟨hnpc, fun h => h, hrc⟩
    rw [callEntry_mem, hmw5] at hk2
    refine ⟨⟨hk2.1.trans hk1.1, fun acc => (hk2.2 acc).trans (hk1.2 acc)⟩, fun hp => ?_⟩
    rcases hlib5.2.2.2.2.1 a hp with h | h
    · exact hnpc h
    · rw [hrc] at h; cases h
  -- the streams up to `error`'s entry
  have hS : ∀ f st, E.S.file s.m.memory f st → E.S.file (callEntry w5 (lb + 0x11e6c0#64) ret5).m.memory f st := by
    intro f st h
    have h1 := hFt f st h
    have h2 : E.S.file e2.m.memory f st := by rw [hme2, hmu]; exact file_push h1 (by rw [hu8]; omega)
    have h3 := hQX.streams f st List.not_mem_nil h2
    have h4 : E.S.file (callEntry w2 (lb + 0x2a6e0#64) (b + 0x6a40#64 + BitVec.ofNat 64 (698 + 5))).m.memory f st := by
      rw [callEntry_mem, hmw2]; exact file_push h3 (by rw [hw28]; omega)
    have h5 := hok3 f st List.not_mem_nil h4
    rw [callEntry_mem, hmw5]; exact file_push h5 (by rw [hw58]; omega)
  have hgs5 : (callEntry w5 (lb + 0x11e6c0#64) ret5).g = s.g := by
    rw [callEntry_g, hgw5, hg3, callEntry_g, hgw2, hQX.g, hge2, hgu, hgt]
  -- the stack frame of `digest_file` up to `v5`
  have hFr : Keeps (fun a => (s.m.core.read .rsp).toNat - 216 ≤ a ∧ a < (s.m.core.read .rsp).toNat) x.m.memory
      v5.m.memory := by
    have hns : ∀ a, (s.m.core.read .rsp).toNat - 216 ≤ a → a < (s.m.core.read .rsp).toNat → ¬ W.Kept a :=
      fun a h1 h2 => hNK a (by omega) (by omega)
    refine hkF.trans ?_
    refine Keeps.trans (m₂ := e2.m.memory) (by rw [hme2, hmu]; exact pushMem_keeps fun a ha => by rw [hu8]; omega) ?_
    refine Keeps.trans (m₂ := t2.m.memory) (hQX.ret.1.2.mono fun a ha => ⟨Or.inr (by rw [he2r]; omega), by
      rintro (h | ⟨h1, h2⟩)
      · exact hns a ha.1 ha.2 (hslotK a h)
      · rw [he2r] at h2; omega⟩) ?_
    refine Keeps.trans (m₂ := (callEntry w2 (lb + 0x2a6e0#64) (b + 0x6a40#64 + BitVec.ofNat 64 (698 + 5))).m.memory)
      (by rw [callEntry_mem, hmw2]; exact pushMem_keeps fun a ha => by rw [hw28]; omega) ?_
    refine Keeps.trans (m₂ := v3.m.memory) (hlib3.1.2.mono fun a ha => ⟨Or.inr (by rw [callEntry_rsp, hw28]; omega),
      fun h => h⟩) ?_
    refine Keeps.trans (m₂ := (callEntry w5 (lb + 0x11e6c0#64) ret5).m.memory)
      (by rw [callEntry_mem, hmw5]; exact pushMem_keeps fun a ha => by rw [hw58]; omega) ?_
    exact hlib5.1.2.mono fun a ha => ⟨Or.inr (by rw [callEntry_rsp, hw58]; omega), fun h => h⟩
  -- `*missing` up to `v5` (above every callee's stack pointer, not the image, not `slot0`)
  have hMXs : ∀ a, MX s a → (s.m.core.read .rsp).toNat + 8 ≤ a ∧ ¬ W.Kept a :=
    fun a h => ⟨(hX a (Or.inl h)).2, (hX a (Or.inl h)).1⟩
  have hMXk : Keeps (MX s) x.m.memory v5.m.memory := by
    refine Keeps.trans (m₂ := t.m.memory) ((hpush.mono fun a ha => Or.inr (by have := (hMXs a ha).1; omega)).trans
      (hkT.mono fun a ha => Or.inr (by
        have := (hMXs a ha).1; show (x.m.core.read .rsp - 8#64).toNat ≤ a; rw [hx8]; omega))) ?_
    refine Keeps.trans (m₂ := e2.m.memory) (by
      rw [hme2, hmu]; exact pushMem_keeps fun a ha => by have := (hMXs a ha).1; rw [hu8]; omega) ?_
    refine Keeps.trans (m₂ := t2.m.memory) (hQX.ret.1.2.mono fun a ha => ⟨Or.inr (by
      have := (hMXs a ha).1; rw [he2r]; omega), by
      rintro (h | ⟨h1, h2⟩)
      · exact (hMXs a ha).2 (hslotK a h)
      · have := (hMXs a ha).1; rw [he2r] at h2; omega⟩) ?_
    refine Keeps.trans (m₂ := (callEntry w2 (lb + 0x2a6e0#64) (b + 0x6a40#64 + BitVec.ofNat 64 (698 + 5))).m.memory)
      (by rw [callEntry_mem, hmw2]; exact pushMem_keeps fun a ha => by have := (hMXs a ha).1; rw [hw28]; omega) ?_
    refine Keeps.trans (m₂ := v3.m.memory) (hlib3.1.2.mono fun a ha => ⟨Or.inr (by
      have := (hMXs a ha).1; rw [callEntry_rsp, hw28]; omega), fun h => h⟩) ?_
    refine Keeps.trans (m₂ := (callEntry w5 (lb + 0x11e6c0#64) ret5).m.memory)
      (by rw [callEntry_mem, hmw5]; exact pushMem_keeps fun a ha => by have := (hMXs a ha).1; rw [hw58]; omega) ?_
    exact hlib5.1.2.mono fun a ha => ⟨Or.inr (by have := (hMXs a ha).1; rw [callEntry_rsp, hw58]; omega), fun h => h⟩
  have hrbp6 : w6.m.core.read .rbp = s.m.core.read .rsp - 8#64 := by
    have hcsr : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, r ≠ .rbx → w6.m.core.read r = u.m.core.read r := by
      intro r hr hne
      rw [hcsw6 r hr, hcs5 r hr, hcsw5 r hr, hcs3 r hr, hcsw2 r hr hne, hcs2 r hr]
    rw [hcsr .rbp (by simp [Silmaril.X86.sysv64_calleeSaved]) (by decide)]; exact hrbpu
  refine dg_epiR I.cl (X := fun a => MX s a ∨ Slot0 b a) (fun m h => h.1)
    (hB5.of_eq hmw6 hspw6 hfsw6 (by rw [hgw6])) hrw6 hrbp6
    (by rw [hmw6, hFr.readBytes (fun j hj => ⟨by omega, by omega⟩)]; exact hM.slot3) hE.abi hE.guard hE.guardk
    (fun j hj => by
      rintro (hm | hs)
      · exact (hX _ (Or.inl hm)).1 (hE.guardk j hj)
      · exact hE.guardq j hj hs)
    (fun j hj => by
      rintro (hm | hs)
      · have := (hX _ (Or.inl hm)).2; omega
      · exact hNK _ (by omega) (by omega) (hslotK _ hs)) ?_
  intro tf habif hmf haxf hgf hfsf
  have hmt : tf.m.memory = v5.m.memory := by rw [hmf, hmw6]
  have hgtf : tf.g = v5.g := by rw [hgf, hgw6]
  refine k tf ⟨habif, by rw [hmt]; exact hB5.keepX, by rw [haxf, hraxw6]; rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hfsf, by rw [hmt]; exact hB5.perm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hgtf, hg5]; simp only; rw [hgs5]
  · rw [hgtf, hg5]; simp only; rw [hgs5]
  · rw [hgtf, hg5]; simp only; rw [hgs5]
  · rw [hgtf, hg5]; simp only; rw [hgs5]
  · rw [hgtf, hg5]; simp only; rw [hgs5]
  · refine appended_post (appended_pre (fun st h => ⟨hS _ _ h.1, h.2⟩) (by rw [hgs5]) happ5)
      (fun st h => by rw [hmt]; exact h) (by rw [hgtf])
  · intro f st hne h
    rw [hmt]; exact hok5 f st (by simpa using hne) (hS f st h)
  · exact hE.slots.keep I.cl.hb (by rw [hmt]; exact hB5.keepX.mono fun a ha =>
      ⟨Or.inl (Or.inl (by rw [I.cl.img]; exact ha.1)), by
        rintro (hm | hs)
        · exact (hX a (Or.inl hm)).1 (Or.inl (by rw [I.cl.img]; exact ha.1))
        · exact ha.2 hs⟩)
  · intro a ha
    rw [hmt]
    obtain ⟨⟨-, hp5⟩, hn5⟩ := hS5 a ha
    obtain ⟨⟨-, hp3⟩, -⟩ := hS3 a ha
    obtain ⟨h1, h2, -⟩ := hQX.slot0 a ha
    exact ⟨by rw [hp5, hp3]; exact h1, by rw [hp5, hp3]; exact h2, hn5⟩
  · rw [hmt]; exact hLKv5.1
  · rw [hmt]; exact hLKv5.2
  · intro a ha acc
    rw [hmt, (hMXk a ha).2 acc]
    unfold Memory.permits; rw [hM.regs]
  · rw [hgtf, hg5]; simp only; rw [hgs5]
  · rw [hgtf, hg5]; simp only; rw [hgs5]
  · rw [hgtf, hg5]; simp only; rw [hgs5]

/-- **`digest_file` on a refused name, for one goal**: as `Task.digestOpenErr`, but `quotef` is
only needed for this name and this goal `Q` (so that a caller can supply it from another
machine, e.g. `procX`, through `ProcX.mustX_of_mustQ`). -/
theorem sha_digestOpenErr_for {E : Env} {R : ShaRep} {W : World} {b lb kb pinA : Word}
    (I : DigImps E R W b lb kb) (K : ErrImps E W lb pinA) {Q : PState → Prop} {s : PState} {p : List Byte}
    (hQ : ∀ s', QEntry E W b lb s' p → (∀ t, QExit E W b s' t p → MustQ W Q t) → MustQ W Q s')
    {e : Silmaril.Apps.Sha256sum.Errno} {g : Word} {prog : List Byte}
    (hE : DigEntryE E W b lb kb pinA s p e g prog)
    (k : ∀ t, DigErrExit E W b s t p e prog → MustQ W Q t) : MustQ W Q s := by
  obtain ⟨c0, hc0⟩ : ∃ c0, s.m.memory.readBytes (s.m.core.read .rdi).toNat 1 = some [c0] := by
    have h := Memory.readBytes_sub_range hE.name.2 (offset := 0) (len := 1) (by omega) (by omega)
    simp only [Nat.add_zero, List.drop_zero] at h
    cases p with
    | nil => exact ⟨0, by simpa using h⟩
    | cons c cs => exact ⟨c, by simpa using h⟩
  refine sha_digest_pro I.cl hE.rip (hE.room.mono (by decide)) hE.done hE.mem (fun u hP => ?_)
  refine sha_digest_mid I hP (by have := hE.lo; omega) (fun j hj => (hE.namek j hj).1) hc0 (hE.notDash c0 hc0)
    hE.outs hE.missw hE.missr hE.guard hE.guardk (fun x hM hrx h14 => ?_)
  exact sha_digest_err I K hQ hE hM hrx h14 k

/-- **`Task.digestOpenErr` holds**: `digest_file` on a name the file system refuses, end to end
(given gnulib's `quotef`, `Task.quotef`). -/
theorem task_digestOpenErr {E : Env} {R : ShaRep} {W : World} {b lb kb pinA : Word} :
    Task.digestOpenErr E R W b lb kb pinA := by
  intro I K hQ Q s p e g prog hE k
  exact sha_digestOpenErr_for I K (fun s' => hQ Q s' p) hE k

end Silmaril.Elf.Link.Dyn.Sha256sum
