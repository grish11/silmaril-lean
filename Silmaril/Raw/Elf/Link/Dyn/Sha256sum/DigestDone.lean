module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.DigestLoop

/-! # GNU `sha256sum`: `digest_file` after the read loop (`done`, from `0x6b2c`)

```
0x6b2c: if (sum > 0) SHA256_Update (ctx, buffer, sum);       // 0x6c90
0x6b35: SHA256_Final (bin_result, ctx); free (buffer);
```
`DigDone`: what holds once the context has absorbed the whole input.
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

/-- At `0x6b35`: the context holds all of `data`, the stream is at its end. -/
structure DigDone (E : Env) (R : ShaRep) (W : World) (b lb kb : Word) (X : Nat → Prop) (s u : PState)
    (F buf g : Word) (z : BitVec 32) (data : List Byte) (st : St) : Prop where
  hX : ∀ x, X x → x + 1024 < (s.m.core.read .rsp).toNat ∨ (s.m.core.read .rsp).toNat + 8 ≤ x
  lo : E.S.lo + 1024 ≤ (s.m.core.read .rsp).toNat
  al : (s.m.core.read .rsp).toNat % 16 = 8
  body : BodyX W (ShaMemCD b lb kb) s u 216 1024 (sv6 s) X
  rbp : u.m.core.read .rbp = s.m.core.read .rsp - 8#64
  rbx : u.m.core.read .rbx = F
  r12 : u.m.core.read .r12 = buf
  r14 : BitVec.setWidth 32 (u.m.core.read .r14) = z
  sbin : u.m.memory.readBytes ((s.m.core.read .rsp).toNat - 200) 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [s.m.core.read .rsi])
  sctx : u.m.memory.readBytes ((s.m.core.read .rsp).toNat - 192) 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [s.m.core.read .rsp - 184#64])
  sg : u.m.memory.readBytes ((s.m.core.read .rsp).toNat - 64) 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [g])
  miss : u.m.memory.readBytes (s.m.core.read .rdx).toNat 1 = some [0#8]
  rdxhi : (s.m.core.read .rsp).toNat + 8 ≤ (s.m.core.read .rdx).toNat
  holds : R.holds u.m.memory (s.m.core.read .rsp - 184#64) data
  file : E.S.file u.m.memory F st
  stok : st.fail = false ∧ st.err = false ∧ st.reading = true ∧ st.fd < 2 ^ 31 ∧ st.rd = []
  g : u.g = s.g.withBlk buf.toNat 0x8048
  others : ∀ f st', f ≠ F → E.S.file s.m.memory f st' → E.S.file u.m.memory f st'
  pdx : PermDX s u.m.memory
  /-- the library variables of the entry are kept -/
  lib : LibK E W s.m.memory u.m.memory
  /-- the buffer holds no library variable of the entry (it was the library's when `malloc` returned it) -/
  buffr : ∀ a, buf.toNat ≤ a → a < buf.toNat + 0x8048 → ¬ LibV E W s.m.memory a

theorem DigInv.toDone {E : Env} {R : ShaRep} {W : World} {b lb kb : Word} {X : Nat → Prop} {s u : PState}
    {F buf g : Word} {z : BitVec 32} {data absorbed : List Byte} {st : St}
    (h : DigInv E R W b lb kb X s u F buf g z data absorbed [] st) (hrd : st.rd = []) :
    DigDone E R W b lb kb X s u F buf g z data st :=
  ⟨h.hX, h.lo, h.al, h.body, h.rbp, h.rbx, h.r12, h.r14, h.sbin, h.sctx, h.sg, h.miss, h.rdxhi,
    by have := h.data; rw [hrd] at this; simp only [List.append_nil] at this; rw [← this]; exact h.holds, h.file,
    ⟨h.stok.1, h.stok.2.1, h.stok.2.2.1, h.stok.2.2.2.1, hrd⟩, h.g, h.others, h.pdx, h.lib, h.buffr⟩

theorem DigDone.congr {E : Env} {R : ShaRep} {W : World} {b lb kb : Word} {X : Nat → Prop} {s u u' : PState}
    {F buf g : Word} {z : BitVec 32} {data : List Byte} {st : St}
    (h : DigDone E R W b lb kb X s u F buf g z data st)
    (hm : u'.m.memory = u.m.memory) (hr : u'.m.core.regs = u.m.core.regs)
    (hf : u'.m.core.fsBase = u.m.core.fsBase) (hg : u'.g = u.g) :
    DigDone E R W b lb kb X s u' F buf g z data st := by
  have hrd : ∀ r, u'.m.core.read r = u.m.core.read r := fun r => by
    show u'.m.core.regs r = u.m.core.regs r; rw [hr]
  exact ⟨h.hX, h.lo, h.al, h.body.of_eq hm (hrd _) hf (by rw [hg]), by rw [hrd]; exact h.rbp,
    by rw [hrd]; exact h.rbx, by rw [hrd]; exact h.r12, by rw [hrd]; exact h.r14,
    hm ▸ h.sbin, hm ▸ h.sctx, hm ▸ h.sg, hm ▸ h.miss, h.rdxhi, hm ▸ h.holds, hm ▸ h.file, h.stok, hg ▸ h.g,
    hm ▸ h.others, hm ▸ h.pdx, hm ▸ h.lib, h.buffr⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- **`done`, the last partial block**: `SHA256_Update (ctx, buffer, sum)` when `sum > 0`. -/
theorem dg_flush {E : Env} {R : ShaRep} {W : World} {b lb kb : Word} (I : DigImps E R W b lb kb)
    {X : Nat → Prop} {Q : PState → Prop} {s x : PState} {F buf g : Word} {z : BitVec 32}
    {data absorbed pend : List Byte} {st : St}
    (hI : DigInv E R W b lb kb X s x F buf g z data absorbed pend st) (hrip : x.m.core.rip = b + 0x6b2c#64)
    (hrd : st.rd = [])
    (k : ∀ v, DigDone E R W b lb kb X s v F buf g z data st → v.m.core.rip = b + 0x6b35#64 → MustQ W Q v) :
    MustQ W Q x := by
  have hin : ∀ n, n < 0xa188 → W.InImage (b + BitVec.ofNat 64 n).toNat := fun n hn => sha_in' I.cl.img I.cl.hb hn
  have hB := hI.body
  have hpl := hI.plen
  have hst : st.fail = false ∧ st.err = false ∧ st.reading = true ∧ st.fd < 2 ^ 31 ∧ st.rd = [] :=
    ⟨hI.stok.1, hI.stok.2.1, hI.stok.2.2.1, hI.stok.2.2.2.1, hrd⟩
  have hdata : absorbed ++ pend = data := by have := hI.data; rw [hrd, List.append_nil] at this; exact this
  have hnz : decide (BitVec.ofNat 64 pend.length = 0#64) = decide (pend = []) := by
    rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, ← List.length_eq_zero_iff]
    constructor
    · intro h; have := congrArg BitVec.toNat h; simp at this; omega
    · intro h; rw [h]
  refine must_listed (o := 236) shaD_listing_ok.2.2 rfl hB.done (by rw [hrip]; exact hin _ (by decide))
    hB.mem.2.digestFile (by rw [hrip, ripadd]) ?_
  xstep [hrip, hI.r15]
  refine must_listed (o := 239) shaD_listing_ok.2.2 rfl hB.done (hin _ (by decide)) hB.mem.2.digestFile (by rw [ripadd]) ?_
  xstep [eval_ne_testQ, hnz]
  by_cases hp0 : pend = []
  · subst hp0
    simp only [decide_true, Bool.not_true]
    exact k _ ((hI.toDone hrd).congr rfl rfl rfl rfl) (by simp)
  · simp only [hp0, decide_false, Bool.not_false]
    have hlo := hI.lo
    have hsv := sv6_bound s
    have hal216 : ((s.m.core.read .rsp).toNat - 216) % 16 = 0 := by have := hI.al; omega
    have hbb := permitted_bound hI.bufr
    have hbelow : buf.toNat + 0x8048 ≤ (s.m.core.read .rsp).toNat - 1024 := by
      have := (hI.bufok (buf.toNat + 0x8047) (by omega) (by omega)).2.1; omega
    have e8 : (s.m.core.read .rsp - 8#64).toNat = (s.m.core.read .rsp).toNat - 8 :=
      sub_toNat (k := 8) (by omega) (by decide)
    have hs192 : (x.m.core.read .rbp + BitVec.signExtend 64 0xffffff48#32).toNat = (s.m.core.read .rsp).toNat - 192 := by
      rw [hI.rbp, show BitVec.signExtend 64 0xffffff48#32 = 0xffffffffffffff48#64 by decide, BitVec.toNat_add, e8]
      simp only [BitVec.toNat_ofNat]; omega
    refine must_listed (o := 592) shaD_listing_ok.2.2 rfl hB.done (hin _ (by decide)) hB.mem.2.digestFile (by rw [ripadd]) ?_
    rw [exec_loadqd _ _ _ _ _ _ _ (by
      show loadN x.m.memory (x.m.core.read .rbp + BitVec.signExtend 64 0xffffff48#32) 8 = some (s.m.core.read .rsp - 184#64)
      exact loadN_of_enc (by rw [hs192]; exact hI.sctx)), WP_ok]
    refine must_listed (o := 599) shaD_listing_ok.2.2 rfl hB.done (by simp only [ripadd]; exact hin _ (by decide))
      hB.mem.2.digestFile (by simp only [ripadd]) ?_
    xstep []
    refine must_listed (o := 602) shaD_listing_ok.2.2 rfl hB.done (hin _ (by decide)) hB.mem.2.digestFile (by rw [ripadd]) ?_
    xstep []
    refine must_gen (fun y => BodyX W (ShaMemCD b lb kb) s y 216 1024 (sv6 s) X ∧ y.m.core.rip = b + 0x6c9d#64 ∧
        y.m.memory = x.m.memory ∧ y.g = x.g ∧
        y.m.core.read .rdi = s.m.core.read .rsp - 184#64 ∧ y.m.core.read .rsi = buf ∧ y.m.core.read .rdx = BitVec.ofNat 64 pend.length ∧
        (∀ r ∈ Silmaril.X86.sysv64.calleeSaved, y.m.core.read r = x.m.core.read r)) ?_ ?_
    · refine ⟨hB.of_eq rfl (by simp) rfl rfl, rfl, rfl, rfl, by simp, ?_, by simp [hI.r15], ?_⟩
      · simp [hI.r12]
      · intro r hr
        simp only [Silmaril.X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    rintro y ⟨hBy, hry, hmy, hgy, hdiy, hsiy, hdxy, hcsy⟩
    have hyr : (y.m.core.read .rsp).toNat = (s.m.core.read .rsp).toNat - 216 := by
      rw [hBy.rsp]; exact sub_toNat (by omega) (by decide)
    have hy8 : (y.m.core.read .rsp - 8#64).toNat = (s.m.core.read .rsp).toNat - 224 := by
      rw [sub_toNat (k := 8) (by rw [hyr]; omega) (by decide), hyr]; omega
    have hlo8 : E.S.lo ≤ (y.m.core.read .rsp - 8#64).toNat := by rw [hy8]; omega
    have hctxN : (s.m.core.read .rsp - 184#64).toNat = (s.m.core.read .rsp).toNat - 184 :=
      sub_toNat (k := 184) (by omega) (by decide)
    -- the memory at the entry of SHA256_Update: the return address pushed
    have hkpush : ∀ {P : Nat → Prop}, (∀ a, P a → a < (s.m.core.read .rsp).toNat - 224 ∨ (s.m.core.read .rsp).toNat - 216 ≤ a) →
        Keeps P y.m.memory (pushMem y.m.memory (y.m.core.read .rsp) (b + 27200#64 + BitVec.ofNat 64 (605 + 5))) :=
      fun hP => pushMem_keeps fun a ha => by rw [hy8]; have := hP a ha; omega
    have hHc : R.holds (pushMem y.m.memory (y.m.core.read .rsp) (b + 27200#64 + BitVec.ofNat 64 (605 + 5)))
        (s.m.core.read .rsp - 184#64) absorbed :=
      R.local_ _ _ _ _ (hkpush fun a ha => by rw [hctxN] at ha; omega) (by rw [hmy]; exact hI.holds)
    have hRc : (pushMem y.m.memory (y.m.core.read .rsp) (b + 27200#64 + BitVec.ofNat 64 (605 + 5))).readBytes
        buf.toNat (BitVec.ofNat 64 pend.length : Word).toNat = some pend := by
      rw [show (BitVec.ofNat 64 pend.length : Word).toNat = pend.length from Nat.mod_eq_of_lt (by omega),
        (hkpush (P := fun a => a < buf.toNat + 0x8048) fun a ha => Or.inl (by omega)).readBytes (fun j hj => by omega),
        hmy]
      exact hI.bufrd
    have hpe : ∀ a, a < E.S.lo → (pushMem y.m.memory (y.m.core.read .rsp) (b + 27200#64 + BitVec.ofNat 64 (605 + 5))).bytes.get? a
        = x.m.memory.bytes.get? a ∧ ∀ acc, (pushMem y.m.memory (y.m.core.read .rsp)
          (b + 27200#64 + BitVec.ofNat 64 (605 + 5))).permits acc a = x.m.memory.permits acc a := by
      intro a ha
      rw [← hmy]
      exact ⟨(pushMem_keeps (P := fun x => x < E.S.lo) (m := y.m.memory) (sp := y.m.core.read .rsp)
        (v := b + 27200#64 + BitVec.ofNat 64 (605 + 5)) (fun x hx => Or.inl (by omega)) a ha).1, fun acc => rfl⟩
    have hpp : E.S.priv (pushMem y.m.memory (y.m.core.read .rsp) (b + 27200#64 + BitVec.ofNat 64 (605 + 5))) =
        E.S.priv x.m.memory := E.S.priv_local _ _ hpe
    have hpushp : ∀ a acc, (pushMem y.m.memory (y.m.core.read .rsp) (b + 27200#64 + BitVec.ofNat 64 (605 + 5))).permits
        acc a = x.m.memory.permits acc a := fun a acc => by rw [← hmy]; rfl
    refine body_callK (shaMemCD_keep I.cl.img I.cl.hb) hBy (by decide) (by decide) hsv hal216 I.cl.lz
      (o := 605) (so := 0x2f0) (pb := b + 0x23c0#64) (fp := ctxRange (s.m.core.read .rsp - 184#64))
      shaD_listing_ok.2.2 rfl (by rw [hry]; exact hin _ (by decide)) (fun m h => h.2.digestFile)
      (by rw [hry, ripadd]) shaC_listing_ok.1 rfl rfl (by simp only [BitVec.add_assoc]; rfl)
      (img_off I.cl.img I.cl.hb (by decide)) (img_off I.cl.img I.cl.hb (by decide)) (fun m h => h.1.plt)
      (fun m h => by
        rw [show b + 0x23c0#64 + BitVec.ofNat 64 (0x2f0 + 4 + 6) + BitVec.signExtend 64 0x7896#32 = b + 0x9f50#64 by
          simp only [BitVec.add_assoc]; rfl]
        exact h.2.shaUpdate)
      I.update.1 I.update.2.1 I.update.2.2.1 (fun r h => framed_imp ((impOk_fn I.update _ r).1 h))
      ?_ ?_ ?_ (fun x h => hI.hX x h) ?_
    · intro he
      refine ⟨⟨he, ?_, ?_, ?_⟩, ?_⟩
      · rw [callEntry_mem, callEntry_read _ _ _ (by decide : Reg.rdi ≠ .rsp), hdiy]; exact ⟨_, hHc⟩
      · rw [callEntry_mem, callEntry_read _ _ _ (by decide : Reg.rsi ≠ .rsp),
          callEntry_read _ _ _ (by decide : Reg.rdx ≠ .rsp), hsiy, hdxy]; exact ⟨_, hRc⟩
      · rw [callEntry_mem, callEntry_read _ _ _ (by decide : Reg.rdi ≠ .rsp), hdiy, pushMem_permitted, hctxN]
        exact room_perm hBy.room (Or.inr rfl) (by omega) (by omega)
      · rw [callEntry_mem, callEntry_read _ _ _ (by decide : Reg.rdi ≠ .rsp), hdiy, hpp]
        intro a ha hp
        have := E.S.priv_lo _ _ hp
        unfold ctxRange at ha; rw [hctxN] at ha; omega
    · intro v hv
      have h1 := hv.2.1.1
      rw [callEntry_read _ _ _ (by decide : Reg.rdi ≠ .rsp), hdiy] at h1
      exact ⟨h1, hv.2.1.2.2.1, by simpa [callEntry] using hv.2.1.2.1, by rw [hv.1.2.2.2]; exact hBy.done⟩
    · intro a ha
      unfold ctxRange at ha; rw [hctxN] at ha
      exact ⟨(hBy.room.2.2 a (by omega) (by omega)).2.2, Or.inl (by omega)⟩
    intro v hv hBv hrv hspv hcsv hkv
    refine must_listed (o := 610) shaD_listing_ok.2.2 rfl hBv.done (by rw [hrv]; exact img_off I.cl.img I.cl.hb (by decide))
      hBv.mem.2.digestFile (by rw [hrv, ripadd]) ?_
    xstep [hrv]
    refine must_gen (fun t => t.m.memory = v.m.memory ∧ t.m.core.read .rsp = v.m.core.read .rsp ∧
        t.m.core.fsBase = v.m.core.fsBase ∧ t.g = v.g ∧ t.m.core.rip = b + 0x6b35#64 ∧
        (∀ r ∈ Silmaril.X86.sysv64.calleeSaved, t.m.core.read r = v.m.core.read r)) ?_ ?_
    · refine ⟨rfl, by simp, rfl, rfl, by simp, ?_⟩
      intro r hr
      simp only [Silmaril.X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    rintro t ⟨hmt, hspt, hfst, hgt, hrt, hcst⟩
    have hreg : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, t.m.core.read r = x.m.core.read r :=
      fun r hr => by rw [hcst r hr, hcsv r hr, hcsy r hr]
    have hupd := hv.1.2.1
    simp only [callEntry_mem, callEntry_read _ _ _ (by decide : Reg.rdi ≠ .rsp),
      callEntry_read _ _ _ (by decide : Reg.rsi ≠ .rsp), callEntry_read _ _ _ (by decide : Reg.rdx ≠ .rsp),
      hdiy, hsiy, hdxy] at hupd
    have hoth := hv.2.2
    unfold OthersKept at hoth; simp only [callEntry_mem] at hoth
    have hgv : v.g = x.g := by rw [hv.1.2.2.2]; simp only [callEntry_g]; exact hgy
    have hk8 : ∀ a, (s.m.core.read .rsp).toNat - 216 ≤ a → a + 8 ≤ (s.m.core.read .rsp).toNat - 184 ∨
        (s.m.core.read .rsp).toNat - 72 ≤ a → v.m.memory.readBytes a 8 = x.m.memory.readBytes a 8 := by
      intro a h1 h2
      rw [hkv.readBytes (fun j hj => ⟨Or.inr (by omega), fun h => by unfold ctxRange at h; rw [hctxN] at h; omega⟩), hmy]
    have hLt : LibK E W s.m.memory t.m.memory := by
      rw [hmt]; exact (hI.lib.of_eq hmy).call hlo8 hv.2.1 fun a ha hf => by
        simp only [callEntry_read _ _ _ (by decide : Reg.rdi ≠ .rsp), hdiy] at hf
        unfold ctxRange at hf; rw [hctxN] at hf; have := ha.1; omega
    refine k t ⟨hI.hX, hI.lo, hI.al, hBv.of_eq hmt hspt hfst (by rw [hgt]), ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, hI.rdxhi, ?_, ?_, hst, ?_, ?_, ?_, hLt, hI.buffr⟩ hrt
    · rw [hreg .rbp (by simp [Silmaril.X86.sysv64_calleeSaved])]; exact hI.rbp
    · rw [hreg .rbx (by simp [Silmaril.X86.sysv64_calleeSaved])]; exact hI.rbx
    · rw [hreg .r12 (by simp [Silmaril.X86.sysv64_calleeSaved])]; exact hI.r12
    · rw [hreg .r14 (by simp [Silmaril.X86.sysv64_calleeSaved])]; exact hI.r14
    · rw [hmt, hk8 _ (by omega) (Or.inl (by omega))]; exact hI.sbin
    · rw [hmt, hk8 _ (by omega) (Or.inl (by omega))]; exact hI.sctx
    · rw [hmt, hk8 _ (by omega) (Or.inr (by omega))]; exact hI.sg
    · rw [hmt, hkv.readBytes (fun j hj => ⟨Or.inr (by have := hI.rdxhi; omega), fun h => by
        unfold ctxRange at h; rw [hctxN] at h; have := hI.rdxhi; omega⟩), hmy]
      exact hI.miss
    · rw [hmt, ← hdata]; exact hupd absorbed pend hHc hRc
    · rw [hmt]; exact hoth F st List.not_mem_nil (file_push (by rw [hmy]; exact hI.file) hlo8)
    · rw [hgt, hgv]; exact hI.g
    · intro f st' hne h
      rw [hmt]; exact hoth f st' List.not_mem_nil (file_push (by rw [hmy]; exact hI.others f st' hne h) hlo8)
    · rw [hmt]; exact (show PermDX s y.m.memory by rw [hmy]; exact hI.pdx).keep hkv
        fun a _ ha => ⟨Or.inr (by omega), fun h => by unfold ctxRange at h; rw [hctxN] at h; omega⟩

theorem _root_.Silmaril.Elf.Link.Dyn.Proc.BodyX.monoX {W : World} {M : Memory → Prop} {s u : PState} {fr n : Nat} {saved : List (Nat × Word)}
    {X X' : Nat → Prop} (h : BodyX W M s u fr n saved X) (hX : ∀ a, X a → X' a) :
    BodyX W M s u fr n saved X' :=
  ⟨h.rsp, h.keepX.mono fun a ha => ⟨ha.1, fun hx => ha.2 (hX a hx)⟩, h.room, h.mem, h.fs, h.done, h.saved, h.perm⟩

/-- The 32 bytes of `bin_result`. -/
def BR (s : PState) (a : Nat) : Prop :=
  (s.m.core.read .rsi).toNat ≤ a ∧ a < (s.m.core.read .rsi).toNat + 32

/-- At `0x6b50` (after `SHA256_Final` and `free`): `bin_result` holds the digest. -/
structure DigFin (E : Env) (W : World) (b lb kb : Word) (X : Nat → Prop) (s u : PState)
    (F g : Word) (z : BitVec 32) (data : List Byte) (st : St) : Prop where
  lo : E.S.lo + 1024 ≤ (s.m.core.read .rsp).toNat
  al : (s.m.core.read .rsp).toNat % 16 = 8
  body : BodyX W (ShaMemCD b lb kb) s u 216 1024 (sv6 s) X
  rbp : u.m.core.read .rbp = s.m.core.read .rsp - 8#64
  rbx : u.m.core.read .rbx = F
  r14 : BitVec.setWidth 32 (u.m.core.read .r14) = z
  sg : u.m.memory.readBytes ((s.m.core.read .rsp).toNat - 64) 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [g])
  miss : u.m.memory.readBytes (s.m.core.read .rdx).toNat 1 = some [0#8]
  bin : u.m.memory.readBytes (s.m.core.read .rsi).toNat 32 = some (sha256 data)
  file : E.S.file u.m.memory F st
  stok : st.fail = false ∧ st.err = false ∧ st.reading = true ∧ st.fd < 2 ^ 31 ∧ st.rd = []
  g : u.g = s.g
  others : ∀ f st', f ≠ F → E.S.file s.m.memory f st' → E.S.file u.m.memory f st'
  pdx : PermDX s u.m.memory
  /-- the library variables of the entry are kept -/
  lib : LibK E W s.m.memory u.m.memory

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- **`SHA256_Final (bin_result, ctx); free (buffer)`** (`0x6b35` → `0x6b50`). `bin_result` is the
caller's: outside `X` so far (its permissions as at entry), inside `X` from here on. -/
theorem dg_final {E : Env} {R : ShaRep} {W : World} {b lb kb : Word} (I : DigImps E R W b lb kb)
    {X : Nat → Prop} {Q : PState → Prop} {s x : PState} {F buf g : Word} {z : BitVec 32}
    {data : List Byte} {st : St}
    (hI : DigDone E R W b lb kb X s x F buf g z data st) (hrip : x.m.core.rip = b + 0x6b35#64)
    (hbX : ∀ a, BR s a → ¬ X a ∧ ¬ W.Kept a ∧ (s.m.core.read .rsp).toNat + 8 ≤ a ∧
      ¬ ((s.m.core.read .rdx).toNat ≤ a ∧ a < (s.m.core.read .rdx).toNat + 1))
    (hbw : s.m.memory.Permitted .write (s.m.core.read .rsi).toNat 32)
    (hbr : s.m.memory.Permitted .read (s.m.core.read .rsi).toNat 32)
    (k : ∀ v, DigFin E W b lb kb (fun a => X a ∨ BR s a) s v F g z data st → v.m.core.rip = b + 0x6b50#64 →
      MustQ W Q v) :
    MustQ W Q x := by
  have hin : ∀ n, n < 0xa188 → W.InImage (b + BitVec.ofNat 64 n).toNat := fun n hn => sha_in' I.cl.img I.cl.hb hn
  have hB0 := hI.body
  have hlo := hI.lo
  have hsv := sv6_bound s
  have hal216 : ((s.m.core.read .rsp).toNat - 216) % 16 = 0 := by have := hI.al; omega
  have e8 : (s.m.core.read .rsp - 8#64).toNat = (s.m.core.read .rsp).toNat - 8 :=
    sub_toNat (k := 8) (by omega) (by decide)
  have hctxN : (s.m.core.read .rsp - 184#64).toNat = (s.m.core.read .rsp).toNat - 184 :=
    sub_toNat (k := 184) (by omega) (by decide)
  have hrdx := hI.rdxhi
  have hbb := permitted_bound hbr
  -- `bin_result`'s permissions are as at entry
  have hbp : ∀ a, BR s a → ∀ acc, x.m.memory.permits acc a = s.m.memory.permits acc a := fun a ha acc =>
    (hB0.keepX a ⟨Or.inr (by have := (hbX a ha).2.2.1; omega), (hbX a ha).1⟩).2 acc
  have hB : BodyX W (ShaMemCD b lb kb) s x 216 1024 (sv6 s) (fun a => X a ∨ BR s a) := hB0.monoX fun a h => Or.inl h
  have hX' : ∀ a, (X a ∨ BR s a) → a + 1024 < (s.m.core.read .rsp).toNat ∨ (s.m.core.read .rsp).toNat + 8 ≤ a := by
    rintro a (h | h)
    · exact hI.hX a h
    · exact Or.inr (hbX a h).2.2.1
  have hs192 : (x.m.core.read .rbp + BitVec.signExtend 64 0xffffff48#32).toNat = (s.m.core.read .rsp).toNat - 192 := by
    rw [hI.rbp, show BitVec.signExtend 64 0xffffff48#32 = 0xffffffffffffff48#64 by decide, BitVec.toNat_add, e8]
    simp only [BitVec.toNat_ofNat]; omega
  have hs200 : (x.m.core.read .rbp + BitVec.signExtend 64 0xffffff40#32).toNat = (s.m.core.read .rsp).toNat - 200 := by
    rw [hI.rbp, show BitVec.signExtend 64 0xffffff40#32 = 0xffffffffffffff40#64 by decide, BitVec.toNat_add, e8]
    simp only [BitVec.toNat_ofNat]; omega
  refine must_listed (o := 245) shaD_listing_ok.2.2 rfl hB.done (by rw [hrip]; exact hin _ (by decide))
    hB.mem.2.digestFile (by rw [hrip, ripadd]) ?_
  rw [exec_loadqd _ _ _ _ _ _ _ (by
    show loadN x.m.memory (x.m.core.read .rbp + BitVec.signExtend 64 0xffffff48#32) 8 = some (s.m.core.read .rsp - 184#64)
    exact loadN_of_enc (by rw [hs192]; exact hI.sctx)), WP_ok]
  refine must_listed (o := 252) shaD_listing_ok.2.2 rfl hB.done (by simp only [hrip, ripadd]; exact hin _ (by decide))
    hB.mem.2.digestFile (by simp only [hrip, ripadd]) ?_
  rw [exec_loadqd _ _ _ _ _ _ _ (by
    show loadN x.m.memory (x.m.core.read .rbp + BitVec.signExtend 64 0xffffff40#32) 8 = some (s.m.core.read .rsi)
    exact loadN_of_enc (by rw [hs200]; exact hI.sbin)), WP_ok]
  refine must_gen (fun y => BodyX W (ShaMemCD b lb kb) s y 216 1024 (sv6 s) (fun a => X a ∨ BR s a) ∧
      y.m.core.rip = b + 0x6b43#64 ∧ y.m.memory = x.m.memory ∧ y.g = x.g ∧
      y.m.core.read .rdi = s.m.core.read .rsi ∧ y.m.core.read .rsi = s.m.core.read .rsp - 184#64 ∧
      (∀ r ∈ Silmaril.X86.sysv64.calleeSaved, y.m.core.read r = x.m.core.read r)) ?_ ?_
  · refine ⟨hB.of_eq rfl (by simp) rfl rfl, by simp [hrip], rfl, rfl, by simp, by simp, ?_⟩
    intro r hr
    simp only [Silmaril.X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  rintro y ⟨hBy, hry, hmy, hgy, hdiy, hsiy, hcsy⟩
  have hyr : (y.m.core.read .rsp).toNat = (s.m.core.read .rsp).toNat - 216 := by
    rw [hBy.rsp]; exact sub_toNat (by omega) (by decide)
  have hy8 : (y.m.core.read .rsp - 8#64).toNat = (s.m.core.read .rsp).toNat - 224 := by
    rw [sub_toNat (k := 8) (by rw [hyr]; omega) (by decide), hyr]; omega
  have hlo8 : E.S.lo ≤ (y.m.core.read .rsp - 8#64).toNat := by rw [hy8]; omega
  have hkpush : ∀ {P : Nat → Prop}, (∀ a, P a → a < (s.m.core.read .rsp).toNat - 224 ∨ (s.m.core.read .rsp).toNat - 216 ≤ a) →
      Keeps P y.m.memory (pushMem y.m.memory (y.m.core.read .rsp) (b + 27200#64 + BitVec.ofNat 64 (259 + 5))) :=
    fun hP => pushMem_keeps fun a ha => by rw [hy8]; have := hP a ha; omega
  have hHc : R.holds (pushMem y.m.memory (y.m.core.read .rsp) (b + 27200#64 + BitVec.ofNat 64 (259 + 5)))
      (s.m.core.read .rsp - 184#64) data :=
    R.local_ _ _ _ _ (hkpush fun a ha => by rw [hctxN] at ha; omega) (by rw [hmy]; exact hI.holds)
  have hpe : ∀ a, a < E.S.lo → (pushMem y.m.memory (y.m.core.read .rsp) (b + 27200#64 + BitVec.ofNat 64 (259 + 5))).bytes.get? a
      = x.m.memory.bytes.get? a ∧ ∀ acc, (pushMem y.m.memory (y.m.core.read .rsp)
        (b + 27200#64 + BitVec.ofNat 64 (259 + 5))).permits acc a = x.m.memory.permits acc a := by
    intro a ha
    rw [← hmy]
    exact ⟨(pushMem_keeps (P := fun x => x < E.S.lo) (m := y.m.memory) (sp := y.m.core.read .rsp)
      (v := b + 27200#64 + BitVec.ofNat 64 (259 + 5)) (fun x hx => Or.inl (by omega)) a ha).1, fun acc => rfl⟩
  have hpp : E.S.priv (pushMem y.m.memory (y.m.core.read .rsp) (b + 27200#64 + BitVec.ofNat 64 (259 + 5))) =
      E.S.priv x.m.memory := E.S.priv_local _ _ hpe
  have hpushp : ∀ a acc, (pushMem y.m.memory (y.m.core.read .rsp) (b + 27200#64 + BitVec.ofNat 64 (259 + 5))).permits
      acc a = x.m.memory.permits acc a := fun a acc => by rw [← hmy]; rfl
  have hbinP : ∀ acc, s.m.memory.Permitted acc (s.m.core.read .rsi).toNat 32 →
      (pushMem y.m.memory (y.m.core.read .rsp) (b + 27200#64 + BitVec.ofNat 64 (259 + 5))).Permitted acc
        (s.m.core.read .rsi).toNat 32 := by
    intro acc h
    unfold Memory.Permitted at h ⊢; rw [Memory.checkSpan_iff] at h ⊢
    exact ⟨h.1, h.2.1, fun j hj => by rw [hpushp, hbp _ ⟨by omega, by omega⟩]; exact h.2.2 j hj⟩
  refine body_callK (shaMemCD_keep I.cl.img I.cl.hb) hBy (by decide) (by decide) hsv hal216 I.cl.lz
    (o := 259) (so := 0x370) (pb := b + 0x23c0#64)
    (fp := fun a => ctxRange (s.m.core.read .rsp - 184#64) a ∨ BR s a)
    shaD_listing_ok.2.2 rfl (by rw [hry]; exact hin _ (by decide)) (fun m h => h.2.digestFile)
    (by rw [hry, ripadd]) shaC_listing_ok.1 rfl rfl (by simp only [BitVec.add_assoc]; rfl)
    (img_off I.cl.img I.cl.hb (by decide)) (img_off I.cl.img I.cl.hb (by decide)) (fun m h => h.1.plt)
    (fun m h => by
      rw [show b + 0x23c0#64 + BitVec.ofNat 64 (0x370 + 4 + 6) + BitVec.signExtend 64 0x7856#32 = b + 0x9f90#64 by
        simp only [BitVec.add_assoc]; rfl]
      exact h.2.shaFinal)
    I.final.1 I.final.2.1 I.final.2.2.1 (fun r h => framed_imp ((impOk_fn I.final _ r).1 h))
    ?_ ?_ ?_ hX' ?_
  · intro he
    refine ⟨⟨he, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [callEntry_mem, callEntry_read _ _ _ (by decide : Reg.rsi ≠ .rsp), hsiy]; exact ⟨_, hHc⟩
    · rw [callEntry_mem, callEntry_read _ _ _ (by decide : Reg.rdi ≠ .rsp), hdiy]; exact hbinP _ hbw
    · rw [callEntry_mem, callEntry_read _ _ _ (by decide : Reg.rdi ≠ .rsp), hdiy]; exact hbinP _ hbr
    · rw [callEntry_mem, callEntry_read _ _ _ (by decide : Reg.rsi ≠ .rsp), hsiy, pushMem_permitted, hctxN]
      exact room_perm hBy.room (Or.inr rfl) (by omega) (by omega)
    · rw [callEntry_mem, callEntry_read _ _ _ (by decide : Reg.rdi ≠ .rsp), hdiy,
        callEntry_read _ _ _ (by decide : Reg.rsi ≠ .rsp), hsiy, hpp]
      intro a ha hp
      have := E.S.priv_lo _ _ hp
      rcases ha with ha | ha
      · unfold ctxRange at ha; rw [hctxN] at ha; omega
      · have := (hbX a ha).2.2.1; omega
  · intro v hv
    have h1 := hv.2.1.1
    rw [callEntry_read _ _ _ (by decide : Reg.rdi ≠ .rsp), hdiy,
      callEntry_read _ _ _ (by decide : Reg.rsi ≠ .rsp), hsiy] at h1
    exact ⟨h1, hv.2.1.2.2.1, by simpa [callEntry] using hv.2.1.2.1, by rw [hv.1.2.2.2]; exact hBy.done⟩
  · rintro a (ha | ha)
    · unfold ctxRange at ha; rw [hctxN] at ha
      exact ⟨(hBy.room.2.2 a (by omega) (by omega)).2.2, Or.inl (by omega)⟩
    · exact ⟨(hbX a ha).2.1, Or.inr (Or.inr ha)⟩
  intro v hv hBv hrv hspv hcsv hkv
  have hfin := hv.1.2.1
  simp only [callEntry_mem, callEntry_read _ _ _ (by decide : Reg.rdi ≠ .rsp),
    callEntry_read _ _ _ (by decide : Reg.rsi ≠ .rsp), hdiy, hsiy] at hfin
  have hbinv : v.m.memory.readBytes (s.m.core.read .rsi).toNat 32 = some (sha256 data) := hfin data hHc
  have hoth := hv.2.2
  unfold OthersKept at hoth; simp only [callEntry_mem] at hoth
  have hgv : v.g = x.g := by rw [hv.1.2.2.2]; simp only [callEntry_g]; exact hgy
  have hLv : LibK E W s.m.memory v.m.memory := (hI.lib.of_eq hmy).call hlo8 hv.2.1 fun a ha hf => by
    simp only [callEntry_read _ _ _ (by decide : Reg.rdi ≠ .rsp), callEntry_read _ _ _ (by decide : Reg.rsi ≠ .rsp),
      hdiy, hsiy] at hf
    have := ha.1
    rcases hf with hf | hf
    · unfold ctxRange at hf; rw [hctxN] at hf; omega
    · have := (hbX a hf).2.2.1; omega
  have hfv : E.S.file v.m.memory F st := hoth F st List.not_mem_nil (file_push (by rw [hmy]; exact hI.file) hlo8)
  have hothv : ∀ f st', f ≠ F → E.S.file s.m.memory f st' → E.S.file v.m.memory f st' := fun f st' hne h =>
    hoth f st' List.not_mem_nil (file_push (by rw [hmy]; exact hI.others f st' hne h) hlo8)
  have hk1 : ∀ a, (s.m.core.read .rsp).toNat - 216 ≤ a → ¬ ctxRange (s.m.core.read .rsp - 184#64) a → ¬ BR s a →
      v.m.memory.bytes.get? a = x.m.memory.bytes.get? a := fun a h1 h2 h3 => by
    rw [(hkv a ⟨Or.inr h1, fun h => h.elim h2 h3⟩).1, hmy]
  refine must_listed (o := 264) shaD_listing_ok.2.2 rfl hBv.done (by rw [hrv]; exact img_off I.cl.img I.cl.hb (by decide))
    hBv.mem.2.digestFile (by rw [hrv, ripadd]) ?_
  xstep [hrv]
  refine must_gen (fun y2 => BodyX W (ShaMemCD b lb kb) s y2 216 1024 (sv6 s) (fun a => X a ∨ BR s a) ∧
      y2.m.core.rip = b + 0x6b4b#64 ∧ y2.m.memory = v.m.memory ∧ y2.g = v.g ∧
      (∀ r ∈ Silmaril.X86.sysv64.calleeSaved, y2.m.core.read r = v.m.core.read r) ∧
      y2.m.core.read .rdi = v.m.core.read .r12) ?_ ?_
  · refine ⟨hBv.of_eq rfl (by simp) rfl rfl, by simp, rfl, rfl, ?_, by simp⟩
    intro r hr
    simp only [Silmaril.X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  rintro y2 ⟨hBy2, hry2, hmy2, hgy2, hcsy2, hdiy2⟩
  have hbuf2 : y2.m.core.read .rdi = buf := by
    rw [hdiy2, hcsv .r12 (by simp [Silmaril.X86.sysv64_calleeSaved]), hcsy .r12 (by simp [Silmaril.X86.sysv64_calleeSaved])]
    exact hI.r12
  have hyr2 : (y2.m.core.read .rsp).toNat = (s.m.core.read .rsp).toNat - 216 := by
    rw [hBy2.rsp]; exact sub_toNat (by omega) (by decide)
  have hy28 : (y2.m.core.read .rsp - 8#64).toNat = (s.m.core.read .rsp).toNat - 224 := by
    rw [sub_toNat (k := 8) (by rw [hyr2]; omega) (by decide), hyr2]; omega
  have hlo28 : E.S.lo ≤ (y2.m.core.read .rsp - 8#64).toNat := by rw [hy28]; omega
  refine body_callK (shaMemCD_keep I.cl.img I.cl.hb) hBy2 (by decide) (by decide) hsv hal216 I.cl.lz
    (o := 267) (so := 0x200) (pb := b + 0x23c0#64)
    (fp := FreedBlk W (callEntry y2 (lb + 0xade30#64) (b + 27200#64 + BitVec.ofNat 64 (267 + 5))))
    shaD_listing_ok.2.2 rfl (by rw [hry2]; exact hin _ (by decide)) (fun m h => h.2.digestFile)
    (by rw [hry2, ripadd]) shaC_listing_ok.1 rfl rfl (by simp only [BitVec.add_assoc]; rfl)
    (img_off I.cl.img I.cl.hb (by decide)) (img_off I.cl.img I.cl.hb (by decide)) (fun m h => h.1.plt)
    (fun m h => by
      rw [show b + 0x23c0#64 + BitVec.ofNat 64 (0x200 + 4 + 6) + BitVec.signExtend 64 0x790e#32 = b + 0x9ed8#64 by
        simp only [BitVec.add_assoc]; rfl]
      exact h.2.free)
    I.free.1 I.free.2.1 I.free.2.2.1 (fun r h => (impOk_fn I.free _ r).1 h)
    (fun he => ⟨he, Or.inr (by
      rw [callEntry_read _ _ _ (by decide : Reg.rdi ≠ .rsp), hbuf2, callEntry_g, hgy2, hgv, hI.g, withBlk_at]; rfl)⟩)
    ?_ (fun a ha => ⟨ha.2.1, Or.inl (by have := ha.2.2; rw [callEntry_rsp, hy28] at this; omega)⟩) hX' ?_
  · intro v2 hv2
    exact ⟨hv2.1.1, hv2.1.2.2.1, by simpa [callEntry] using hv2.1.2.1, by rw [hv2.2.1]; exact hBy2.done⟩
  intro v2 hv2 hBv2 hrv2 hspv2 hcsv2 hkv2
  have hLc2 : LibK E W s.m.memory
      (callEntry y2 (lb + 0xade30#64) (b + 27200#64 + BitVec.ofNat 64 (267 + 5))).m.memory := by
    rw [callEntry_mem]; exact (hLv.of_eq hmy2).push hlo28
  have hLv2 : LibK E W s.m.memory v2.m.memory := hLc2.freeRet hv2.1 fun a ha hf => by
    obtain ⟨⟨n, hn, h1, h2⟩, -, -⟩ := hf
    simp only [callEntry_g, callEntry_read _ _ _ (by decide : Reg.rdi ≠ .rsp), hbuf2] at hn h1 h2
    rw [hgy2, hgv, hI.g, withBlk_at] at hn
    have hn' := Option.some.inj hn; subst hn'
    exact hI.buffr a h1 h2 ha
  have hoth2 := hv2.2.2
  unfold OthersKept at hoth2; simp only [callEntry_mem] at hoth2
  have hk2 : ∀ a, (s.m.core.read .rsp).toNat - 216 ≤ a → v2.m.memory.bytes.get? a = v.m.memory.bytes.get? a :=
    fun a h1 => by rw [(hkv2 a ⟨Or.inr h1, fun h => by have := h.2.2; rw [callEntry_rsp, hy28] at this; omega⟩).1, hmy2]
  have hreg : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, v2.m.core.read r = x.m.core.read r :=
    fun r hr => by rw [hcsv2 r hr, hcsy2 r hr, hcsv r hr, hcsy r hr]
  have hrb : ∀ a n, (∀ j, j < n → (s.m.core.read .rsp).toNat - 216 ≤ a + j ∧
      ¬ ctxRange (s.m.core.read .rsp - 184#64) (a + j) ∧ ¬ BR s (a + j)) →
      v2.m.memory.readBytes a n = x.m.memory.readBytes a n := by
    intro a n h
    have k1 : Keeps (fun c => (s.m.core.read .rsp).toNat - 216 ≤ c ∧ ¬ ctxRange (s.m.core.read .rsp - 184#64) c ∧
        ¬ BR s c) x.m.memory v.m.memory := by
      rw [← hmy]
      exact hkv.mono fun c hc => ⟨Or.inr hc.1, fun h => h.elim hc.2.1 hc.2.2⟩
    have k2 : Keeps (fun c => (s.m.core.read .rsp).toNat - 216 ≤ c) v.m.memory v2.m.memory := by
      rw [← hmy2]
      exact hkv2.mono fun c hc => ⟨Or.inr hc, fun h => by have := h.2.2; rw [callEntry_rsp, hy28] at this; omega⟩
    rw [(k1.trans (k2.mono fun c hc => hc.1)).readBytes h]
  have hpdv : PermDX s v.m.memory := by
    obtain ⟨-, -, -, -, -, hperm, -⟩ := hv.2.1
    simp only [callEntry_mem, hpp] at hperm
    refine ⟨hI.pdx.pos, fun a ha acc => ?_⟩
    have hpos := hI.pdx.pos a ha
    by_cases hb' : BR s a
    · have hnp : ¬ E.S.priv x.m.memory a := fun hp => by have := E.S.priv_lo _ _ hp; omega
      have hrd : (pushMem y.m.memory (y.m.core.read .rsp) (b + 27200#64 + BitVec.ofNat 64 (259 + 5))).permits .read a
          = true := by
        rw [hpushp, hI.pdx.perm a ha]
        have := hbr; unfold Memory.Permitted at this; rw [Memory.checkSpan_iff] at this
        unfold BR at hb'
        have h := this.2.2 (a - (s.m.core.read .rsi).toNat) (by omega)
        rwa [show (s.m.core.read .rsi).toNat + (a - (s.m.core.read .rsi).toNat) = a by omega] at h
      rw [hperm a hnp hrd acc, hpushp]; exact hI.pdx.perm a ha acc
    · rw [(hkv a ⟨Or.inr (by omega), fun h => h.elim (fun h => by unfold ctxRange at h; rw [hctxN] at h; omega) hb'⟩).2 acc,
        hmy]
      exact hI.pdx.perm a ha acc
  have hpdv2 : PermDX s v2.m.memory :=
    (show PermDX s y2.m.memory by rw [hmy2]; exact hpdv).keep hkv2 fun a _ ha => ⟨Or.inr (by omega), fun h => by
      have := h.2.2; rw [callEntry_rsp, hy28] at this; omega⟩
  refine k v2 ⟨hI.lo, hI.al, hBv2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI.stok, ?_, ?_, hpdv2, hLv2⟩
    (by rw [hrv2]; simp only [BitVec.add_assoc]; rfl)
  · rw [hreg .rbp (by simp [Silmaril.X86.sysv64_calleeSaved])]; exact hI.rbp
  · rw [hreg .rbx (by simp [Silmaril.X86.sysv64_calleeSaved])]; exact hI.rbx
  · rw [hreg .r14 (by simp [Silmaril.X86.sysv64_calleeSaved])]; exact hI.r14
  · rw [hrb _ _ fun j hj => ⟨by omega, fun h => by unfold ctxRange at h; rw [hctxN] at h; omega,
      fun h => by have := (hbX _ h).2.2.1; omega⟩]
    exact hI.sg
  · rw [hrb _ _ fun j hj => ⟨by omega, fun h => by unfold ctxRange at h; rw [hctxN] at h; omega,
      fun h => (hbX _ h).2.2.2 ⟨by omega, by omega⟩⟩]
    exact hI.miss
  · have k2 : Keeps (fun c => (s.m.core.read .rsp).toNat - 216 ≤ c) v.m.memory v2.m.memory := by
      rw [← hmy2]
      exact hkv2.mono fun c hc => ⟨Or.inr hc, fun h => by have := h.2.2; rw [callEntry_rsp, hy28] at this; omega⟩
    rw [k2.readBytes fun j hj => by unfold BR at *; have := (hbX (s.m.core.read .rsi).toNat ⟨le_refl _, by omega⟩).2.2.1; omega]
    exact hbinv
  · exact hoth2 F st List.not_mem_nil (file_push (by rw [hmy2]; exact hfv) hlo28)
  · rw [hv2.2.1]; simp only [callEntry_g, callEntry_read _ _ _ (by decide : Reg.rdi ≠ .rsp), hbuf2]
    rw [hgy2, hgv, hI.g, withBlk_erase]
  · intro f st' hne h
    exact hoth2 f st' List.not_mem_nil (file_push (by rw [hmy2]; exact hothv f st' hne h) hlo28)

end Silmaril.Elf.Link.Dyn.Sha256sum
