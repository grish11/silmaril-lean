module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.DigestSpec
public import Silmaril.Raw.Elf.Link.Dyn.Proc.Exec

/-! # GNU `sha256sum`: the end of one read in `digest_file` (from `0x6b11`)

A full block goes to `SHA256_Update`; a short read goes back to the loop head or, at end of
file, to `done`. Also the small lemmas the read loop shares.
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

theorem DigInv.congr {E : Env} {R : ShaRep} {W : World} {b lb kb : Word} {X : Nat → Prop} {s u u' : PState}
    {F buf g : Word} {z : BitVec 32} {data absorbed pending : List Byte} {st : St}
    (h : DigInv E R W b lb kb X s u F buf g z data absorbed pending st)
    (hm : u'.m.memory = u.m.memory) (hr : u'.m.core.regs = u.m.core.regs)
    (hf : u'.m.core.fsBase = u.m.core.fsBase) (hg : u'.g = u.g) :
    DigInv E R W b lb kb X s u' F buf g z data absorbed pending st := by
  have hrd : ∀ r, u'.m.core.read r = u.m.core.read r := fun r => by
    show u'.m.core.regs r = u.m.core.regs r; rw [hr]
  exact ⟨h.hX, h.lo, h.al, h.body.of_eq hm (hrd _) hf (by rw [hg]), by rw [hrd]; exact h.rbp,
    by rw [hrd]; exact h.rbx, by rw [hrd]; exact h.r12, by rw [hrd]; exact h.r13, by rw [hrd]; exact h.r14,
    by rw [hrd]; exact h.r15, h.plen, hm ▸ h.sbin, hm ▸ h.sctx, hm ▸ h.sg, hm ▸ h.miss, h.rdxhi, hm ▸ h.holds,
    hm ▸ h.bufrd, hm ▸ h.bufr, hm ▸ h.bufw, hm ▸ h.bufok, hm ▸ h.file, h.stok, h.data, hg ▸ h.g,
    hm ▸ h.others, hm ▸ h.pdx, hm ▸ h.lib, h.buffr⟩

theorem readSt_fst (st : St) (n : Nat) : (readSt st n).1 = st.rd.take n := by
  simp only [readSt]; split <;> rfl

/-- `cmp r64, r64` as the semantics builds it. -/
abbrev cmpQ (x y : BitVec 64) : Silmaril.X86.Flags :=
  @Silmaril.X86.Ext.AluOp.flagsN Silmaril.X86.Ext.Sz.q.bits Silmaril.X86.AluOp.cmp x y

theorem eval_cmpQ (x y : BitVec 64) (c : Silmaril.X86.Ext.Cond) :
    Silmaril.X86.Ext.Cond.eval (cmpQ x y) c = some (Silmaril.X86.Ext.Cond.afterCmp (w := 63) x y c) :=
  Silmaril.X86.Ext.eval_subFlagsN (w := 63) x y c

theorem eval_cmp64 (x y : BitVec 64) (c : Silmaril.X86.Ext.Cond) :
    Silmaril.X86.Ext.Cond.eval (@Silmaril.X86.Ext.AluOp.flagsN 64 Silmaril.X86.AluOp.cmp x y) c =
      some (Silmaril.X86.Ext.Cond.afterCmp (w := 63) x y c) :=
  Silmaril.X86.Ext.eval_subFlagsN (w := 63) x y c


theorem readBytes_nil' {m : Memory} {a : Nat} (h : a < 2 ^ 64) : m.readBytes a 0 = some [] := by
  simp [Memory.readBytes, Memory.readWith, Memory.checkSpan, Memory.readBacking,
    Silmaril.Process.addressLimit]
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- **After a read** (`0x6b11`, `sum` updated): a full block goes to `SHA256_Update` and back to
the head with nothing pending; otherwise to the head (`n ≠ 0`) or, at the end of the input, to
`done` (`n = 0`, no error). -/
theorem dg_after {E : Env} {R : ShaRep} {W : World} {b lb kb : Word} (I : DigImps E R W b lb kb)
    {X : Nat → Prop} {Q : PState → Prop} {s x : PState} {F buf g : Word} {z : BitVec 32}
    {data absorbed pend : List Byte} {st : St}
    (hI : DigInv E R W b lb kb X s x F buf g z data absorbed pend st) (hrip : x.m.core.rip = b + 0x6b11#64)
    {n : Nat} (hrax : x.m.core.read .rax = BitVec.ofNat 64 n) (hn : n ≤ 0x8000)
    (kFull : pend.length = 0x8000 → ∀ v, DigInv E R W b lb kb X s v F buf g z data (absorbed ++ pend) [] st →
      v.m.core.rip = b + 0x6b27#64 → MustQ W Q v)
    (kMore : pend.length < 0x8000 → n ≠ 0 → ∀ v, DigInv E R W b lb kb X s v F buf g z data absorbed pend st →
      v.m.core.rip = b + 0x6b27#64 → MustQ W Q v)
    (kZero : pend.length < 0x8000 → n = 0 → ∀ v, DigInv E R W b lb kb X s v F buf g z data absorbed pend st →
      v.m.core.rip = b + 0x6b2c#64 → MustQ W Q v) :
    MustQ W Q x := by
  have hin : ∀ n, n < 0xa188 → W.InImage (b + BitVec.ofNat 64 n).toNat := fun n hn => sha_in' I.cl.img I.cl.hb hn
  have hB := hI.body
  have hpl := hI.plen
  have hcmp : Silmaril.X86.Ext.Cond.afterCmp (w := 63) (BitVec.ofNat 64 pend.length) 32768#64 .e =
      decide (pend.length = 32768) := by
    simp only [Silmaril.X86.Ext.Cond.afterCmp]
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    constructor
    · intro he; have := congrArg BitVec.toNat he; simp at this; omega
    · intro h; rw [h]
  refine must_listed (o := 209) shaD_listing_ok.2.2 rfl hB.done (by rw [hrip]; exact hin _ (by decide))
    hB.mem.2.digestFile (by rw [hrip, ripadd]) ?_
  xstep [hrip, hI.r15]
  refine must_listed (o := 216) shaD_listing_ok.2.2 rfl hB.done (hin _ (by decide)) hB.mem.2.digestFile (by rw [ripadd]) ?_
  xstep [eval_cmpQ, eval_cmp64, hcmp]
  by_cases hfull : pend.length = 32768
  · -- a full block: SHA256_Update (ctx, buffer, BLOCKSIZE)
    simp only [hfull, decide_true]
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
    refine must_listed (o := 496) shaD_listing_ok.2.2 rfl hB.done (hin _ (by decide)) hB.mem.2.digestFile (by rw [ripadd]) ?_
    rw [exec_loadqd _ _ _ _ _ _ _ (by
      show loadN x.m.memory (x.m.core.read .rbp + BitVec.signExtend 64 0xffffff48#32) 8 = some (s.m.core.read .rsp - 184#64)
      exact loadN_of_enc (by rw [hs192]; exact hI.sctx)), WP_ok]
    refine must_listed (o := 503) shaD_listing_ok.2.2 rfl hB.done (by simp only [ripadd]; exact hin _ (by decide))
      hB.mem.2.digestFile (by simp only [ripadd]) ?_
    xstep []
    refine must_listed (o := 508) shaD_listing_ok.2.2 rfl hB.done (hin _ (by decide)) hB.mem.2.digestFile (by rw [ripadd]) ?_
    xstep []
    refine must_gen (fun y => BodyX W (ShaMemCD b lb kb) s y 216 1024 (sv6 s) X ∧ y.m.core.rip = b + 0x6c3f#64 ∧
        y.m.memory = x.m.memory ∧ y.g = x.g ∧
        y.m.core.read .rdi = s.m.core.read .rsp - 184#64 ∧ y.m.core.read .rsi = buf ∧ y.m.core.read .rdx = 0x8000#64 ∧
        (∀ r ∈ Silmaril.X86.sysv64.calleeSaved, y.m.core.read r = x.m.core.read r)) ?_ ?_
    · refine ⟨hB.of_eq rfl (by simp) rfl rfl, rfl, rfl, rfl, by simp, ?_, by simp, ?_⟩
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
        Keeps P y.m.memory (pushMem y.m.memory (y.m.core.read .rsp) (b + 27200#64 + BitVec.ofNat 64 (511 + 5))) :=
      fun hP => pushMem_keeps fun a ha => by rw [hy8]; have := hP a ha; omega
    have hHc : R.holds (pushMem y.m.memory (y.m.core.read .rsp) (b + 27200#64 + BitVec.ofNat 64 (511 + 5)))
        (s.m.core.read .rsp - 184#64) absorbed :=
      R.local_ _ _ _ _ (hkpush fun a ha => by rw [hctxN] at ha; omega) (by rw [hmy]; exact hI.holds)
    have hRc : (pushMem y.m.memory (y.m.core.read .rsp) (b + 27200#64 + BitVec.ofNat 64 (511 + 5))).readBytes
        buf.toNat (0x8000#64 : Word).toNat = some pend := by
      rw [show (0x8000#64 : Word).toNat = pend.length by rw [hfull]; rfl,
        (hkpush (P := fun a => a < buf.toNat + 0x8048) fun a ha => Or.inl (by omega)).readBytes (fun j hj => by omega),
        hmy]
      exact hI.bufrd
    have hpe : ∀ a, a < E.S.lo → (pushMem y.m.memory (y.m.core.read .rsp) (b + 27200#64 + BitVec.ofNat 64 (511 + 5))).bytes.get? a
        = x.m.memory.bytes.get? a ∧ ∀ acc, (pushMem y.m.memory (y.m.core.read .rsp)
          (b + 27200#64 + BitVec.ofNat 64 (511 + 5))).permits acc a = x.m.memory.permits acc a := by
      intro a ha
      rw [← hmy]
      exact ⟨(pushMem_keeps (P := fun x => x < E.S.lo) (m := y.m.memory) (sp := y.m.core.read .rsp)
        (v := b + 27200#64 + BitVec.ofNat 64 (511 + 5)) (fun x hx => Or.inl (by omega)) a ha).1, fun acc => rfl⟩
    have hpp : E.S.priv (pushMem y.m.memory (y.m.core.read .rsp) (b + 27200#64 + BitVec.ofNat 64 (511 + 5))) =
        E.S.priv x.m.memory := E.S.priv_local _ _ hpe
    have hpushp : ∀ a acc, (pushMem y.m.memory (y.m.core.read .rsp) (b + 27200#64 + BitVec.ofNat 64 (511 + 5))).permits
        acc a = x.m.memory.permits acc a := fun a acc => by rw [← hmy]; rfl
    refine body_callK (shaMemCD_keep I.cl.img I.cl.hb) hBy (by decide) (by decide) hsv hal216 I.cl.lz
      (o := 511) (so := 0x2f0) (pb := b + 0x23c0#64) (fp := ctxRange (s.m.core.read .rsp - 184#64))
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
    refine must_listed (o := 516) shaD_listing_ok.2.2 rfl hBv.done (by rw [hrv]; exact img_off I.cl.img I.cl.hb (by decide))
      hBv.mem.2.digestFile (by rw [hrv, ripadd]) ?_
    xstep [hrv]
    refine must_listed (o := 157) shaD_listing_ok.2.2 rfl hBv.done (hin _ (by decide)) hBv.mem.2.digestFile (by rw [ripadd]) ?_
    xstep []
    refine must_listed (o := 160) shaD_listing_ok.2.2 rfl hBv.done (hin _ (by decide)) hBv.mem.2.digestFile (by rw [ripadd]) ?_
    xstep []
    refine must_gen (fun t => t.m.memory = v.m.memory ∧ t.m.core.read .rsp = v.m.core.read .rsp ∧
        t.m.core.fsBase = v.m.core.fsBase ∧ t.g = v.g ∧ t.m.core.rip = b + 0x6b27#64 ∧ t.m.core.read .r15 = 0#64 ∧
        (∀ r ∈ Silmaril.X86.sysv64.calleeSaved, r ≠ .r15 → t.m.core.read r = v.m.core.read r)) ?_ ?_
    · refine ⟨rfl, by simp, rfl, rfl, by simp, by simp [Silmaril.X86.Ext.AluOp.resultN], ?_⟩
      intro r hr hne
      simp only [Silmaril.X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | exact absurd rfl hne | simp
    rintro t ⟨hmt, hspt, hfst, hgt, hrt, h15t, hcst⟩
    have hreg : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, r ≠ .r15 → t.m.core.read r = x.m.core.read r :=
      fun r hr hne => by rw [hcst r hr hne, hcsv r hr, hcsy r hr]
    obtain ⟨-, -, -, -, hpg, hperm, -⟩ := hv.2.1
    simp only [callEntry_mem, hpp] at hpg hperm
    have hupd := hv.1.2.1
    simp only [callEntry_mem, callEntry_read _ _ _ (by decide : Reg.rdi ≠ .rsp),
      callEntry_read _ _ _ (by decide : Reg.rsi ≠ .rsp), callEntry_read _ _ _ (by decide : Reg.rdx ≠ .rsp),
      hdiy, hsiy, hdxy] at hupd
    have hoth := hv.2.2
    unfold OthersKept at hoth; simp only [callEntry_mem] at hoth
    have hgv : v.g = x.g := by rw [hv.1.2.2.2]; simp only [callEntry_g]; exact hgy
    -- the frame outside the context, kept
    have hk8 : ∀ a, (s.m.core.read .rsp).toNat - 216 ≤ a → a + 8 ≤ (s.m.core.read .rsp).toNat - 184 ∨
        (s.m.core.read .rsp).toNat - 72 ≤ a → v.m.memory.readBytes a 8 = x.m.memory.readBytes a 8 := by
      intro a h1 h2
      rw [hkv.readBytes (fun j hj => ⟨Or.inr (by omega), fun h => by unfold ctxRange at h; rw [hctxN] at h; omega⟩), hmy]
    have hbmapped : ∀ a, buf.toNat ≤ a → a < buf.toNat + 0x8048 → x.m.memory.permits .read a = true := by
      intro a h1 h2
      have := hI.bufr; unfold Memory.Permitted at this; rw [Memory.checkSpan_iff] at this
      have h := this.2.2 (a - buf.toNat) (by omega); rwa [show buf.toNat + (a - buf.toNat) = a by omega] at h
    have hbperm : ∀ a, buf.toNat ≤ a → a < buf.toNat + 0x8048 → ∀ acc, v.m.memory.permits acc a = x.m.memory.permits acc a := by
      intro a h1 h2 acc
      rw [hperm a (hI.bufok a h1 h2).2.2.2 (by rw [hpushp]; exact hbmapped a h1 h2) acc, hpushp]
    have hLt : LibK E W s.m.memory t.m.memory := by
      rw [hmt]; exact (hI.lib.of_eq hmy).call hlo8 hv.2.1 fun a ha hf => by
        simp only [callEntry_read _ _ _ (by decide : Reg.rdi ≠ .rsp), hdiy] at hf
        unfold ctxRange at hf; rw [hctxN] at hf; have := ha.1; omega
    refine kFull hfull t ⟨hI.hX, hI.lo, hI.al, hBv.of_eq hmt hspt hfst (by rw [hgt]), ?_, ?_, ?_, ?_, ?_, ?_, by simp,
      ?_, ?_, ?_, ?_, hI.rdxhi, ?_, ?_, ?_, ?_, ?_, ?_, hI.stok, by rw [List.append_nil]; exact hI.data, ?_, ?_, ?_,
      hLt, hI.buffr⟩ hrt
    · rw [hreg .rbp (by simp [Silmaril.X86.sysv64_calleeSaved]) (by decide)]; exact hI.rbp
    · rw [hreg .rbx (by simp [Silmaril.X86.sysv64_calleeSaved]) (by decide)]; exact hI.rbx
    · rw [hreg .r12 (by simp [Silmaril.X86.sysv64_calleeSaved]) (by decide)]; exact hI.r12
    · rw [hreg .r13 (by simp [Silmaril.X86.sysv64_calleeSaved]) (by decide)]; exact hI.r13
    · rw [hreg .r14 (by simp [Silmaril.X86.sysv64_calleeSaved]) (by decide)]; exact hI.r14
    · rw [h15t]; rfl
    · rw [hmt, hk8 _ (by omega) (Or.inl (by omega))]; exact hI.sbin
    · rw [hmt, hk8 _ (by omega) (Or.inl (by omega))]; exact hI.sctx
    · rw [hmt, hk8 _ (by omega) (Or.inr (by omega))]; exact hI.sg
    · rw [hmt, hkv.readBytes (fun j hj => ⟨Or.inr (by have := hI.rdxhi; omega), fun h => by
        unfold ctxRange at h; rw [hctxN] at h; have := hI.rdxhi; omega⟩), hmy]
      exact hI.miss
    · rw [hmt]; exact hupd absorbed pend hHc hRc
    · exact readBytes_nil' (by omega)
    · have := hI.bufr; unfold Memory.Permitted at this ⊢; rw [Memory.checkSpan_iff] at this ⊢
      exact ⟨this.1, this.2.1, fun j hj => by rw [hmt, hbperm _ (by omega) (by omega)]; exact this.2.2 j hj⟩
    · have := hI.bufw; unfold Memory.Permitted at this ⊢; rw [Memory.checkSpan_iff] at this ⊢
      exact ⟨this.1, this.2.1, fun j hj => by rw [hmt, hbperm _ (by omega) (by omega)]; exact this.2.2 j hj⟩
    · intro a h1 h2
      have hb := hI.bufok a h1 h2
      refine ⟨hb.1, hb.2.1, hb.2.2.1, fun hp => ?_⟩
      rw [hmt] at hp
      rcases hpg a hp with h | h
      · exact hb.2.2.2 h
      · rw [hpushp, hbmapped a h1 h2] at h; cases h
    · rw [hmt]; exact hoth F st List.not_mem_nil (file_push (by rw [hmy]; exact hI.file) hlo8)
    · rw [hgt, hgv]; exact hI.g
    · intro f st' hne h
      rw [hmt]; exact hoth f st' List.not_mem_nil (file_push (by rw [hmy]; exact hI.others f st' hne h) hlo8)
    · rw [hmt]; exact (show PermDX s y.m.memory by rw [hmy]; exact hI.pdx).keep hkv
        fun a _ ha => ⟨Or.inr (by omega), fun h => by unfold ctxRange at h; rw [hctxN] at h; omega⟩
  · simp only [hfull, decide_false]
    have hlt : pend.length < 0x8000 := by omega
    have hnz : decide (BitVec.ofNat 64 n = 0#64) = decide (n = 0) := by
      rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
      constructor
      · intro h; have := congrArg BitVec.toNat h; simp at this; omega
      · intro h; rw [h]
    refine must_listed (o := 222) shaD_listing_ok.2.2 rfl hB.done (hin _ (by decide)) hB.mem.2.digestFile (by rw [ripadd]) ?_
    xstep [hrax]
    refine must_listed (o := 225) shaD_listing_ok.2.2 rfl hB.done (hin _ (by decide)) hB.mem.2.digestFile (by rw [ripadd]) ?_
    xstep [eval_e_testQ, hnz]
    by_cases hn0 : n = 0
    · simp only [hn0, decide_true]
      obtain ⟨fl, hfl, -, hfl5, -⟩ := E.S.flags1 _ _ _ hI.file
      have hz : decide ((fl.setWidth 8 &&& BitVec.ofNat 8 (2 ^ 5)) = 0#8) = true := by
        rw [decide_eq_true_eq, testbit_and (by decide), hfl5, hI.stok.2.1]
      refine must_listed (o := 528) shaD_listing_ok.2.2 rfl hB.done (hin _ (by decide)) hB.mem.2.digestFile (by rw [ripadd]) ?_
      rw [exec_testI8m _ _ _ _ _ fl (by show loadN x.m.memory (x.m.core.read .rbx) 1 = some fl; rw [hI.rbx]; exact hfl), WP_ok]
      refine must_listed (o := 531) shaD_listing_ok.2.2 rfl hB.done (by simp only [ripadd]; exact hin _ (by decide))
        hB.mem.2.digestFile (by simp only [ripadd]) ?_
      xstep [eval_testFlags8 fl _ .e (Or.inl rfl), show (0x20#8 : BitVec 8) = BitVec.ofNat 8 (2 ^ 5) from rfl, hz]
      exact kZero hlt hn0 _ (hI.congr rfl rfl rfl rfl) (by simp)
    · simp only [hn0, decide_false]
      exact kMore hlt hn0 _ (hI.congr rfl rfl rfl rfl) (by simp)

end Silmaril.Elf.Link.Dyn.Sha256sum
