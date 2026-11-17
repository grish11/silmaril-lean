module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.DigestLoop

/-! # GNU `sha256sum`: `digest_file` from the buffer to the loop head (`0x6ac1` → `0x6b27`)

```
0x6ac1: ctx on the stack (rbp - 0xb0); r13 = BLOCKSIZE; SHA256_Init (ctx); sum = 0;
```
Common to standard input and a named file: both reach `0x6ac1` with the buffer just allocated.
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

theorem file_store {E : Env} {m : Memory} {f : Word} {st : St} (h : E.S.file m f st) {a : Word} {k : Nat}
    {v : Word} (hlo : E.S.lo ≤ a.toNat) : E.S.file (storeMem m a k v) f st :=
  (E.S.local_ _ _ _ _ (storeMem_keeps fun x hx => Or.inl (by
    have := E.S.foot_lo _ _ _ _ h hx; omega)) h).1

/-- At `0x6ac1`: the buffer allocated, the stream `F` open on the whole input `data`. -/
structure DigPre (E : Env) (W : World) (b lb kb : Word) (X : Nat → Prop) (s u : PState)
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
  sg : u.m.memory.readBytes ((s.m.core.read .rsp).toNat - 64) 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [g])
  miss : u.m.memory.readBytes (s.m.core.read .rdx).toNat 1 = some [0#8]
  rdxhi : (s.m.core.read .rsp).toNat + 8 ≤ (s.m.core.read .rdx).toNat
  bufr : u.m.memory.Permitted .read buf.toNat 0x8048
  bufw : u.m.memory.Permitted .write buf.toNat 0x8048
  bufok : ∀ a, buf.toNat ≤ a → a < buf.toNat + 0x8048 →
    ¬ W.Kept a ∧ a + 0x100000 < (s.m.core.read .rsp).toNat ∧ a < E.S.lo ∧ ¬ E.S.priv u.m.memory a
  file : E.S.file u.m.memory F st
  stok : st.fail = false ∧ st.err = false ∧ st.reading = true ∧ st.fd < 2 ^ 31 ∧
    (st.eof = true → st.rd = [])
  data : st.rd = data
  g : u.g = s.g.withBlk buf.toNat 0x8048
  others : ∀ f st', f ≠ F → E.S.file s.m.memory f st' → E.S.file u.m.memory f st'
  pdx : PermDX s u.m.memory
  /-- the library variables of the entry are kept -/
  lib : LibK E W s.m.memory u.m.memory
  /-- the buffer holds no library variable of the entry (it was the library's when `malloc` returned it) -/
  buffr : ∀ a, buf.toNat ≤ a → a < buf.toNat + 0x8048 → ¬ LibV E W s.m.memory a

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- **`SHA256_Init (ctx)`, `sum = 0`**: to the loop head with nothing absorbed. -/
theorem dg_init {E : Env} {R : ShaRep} {W : World} {b lb kb : Word} (I : DigImps E R W b lb kb)
    {X : Nat → Prop} {Q : PState → Prop} {s x : PState} {F buf g : Word} {z : BitVec 32}
    {data : List Byte} {st : St}
    (hI : DigPre E W b lb kb X s x F buf g z data st) (hrip : x.m.core.rip = b + 0x6ac1#64)
    (k : ∀ v, DigInv E R W b lb kb X s v F buf g z data [] [] st → v.m.core.rip = b + 0x6b27#64 → MustQ W Q v) :
    MustQ W Q x := by
  have hin : ∀ n, n < 0xa188 → W.InImage (b + BitVec.ofNat 64 n).toNat := fun n hn => sha_in' I.cl.img I.cl.hb hn
  have hB := hI.body
  have hlo := hI.lo
  have hsv := sv6_bound s
  have hsvb : ∀ q ∈ sv6 s, q.1 ≤ 48 := fun q hq => (hsv q hq).1
  have hMk := shaMemCD_keep (lb := lb) (kb := kb) I.cl.img I.cl.hb
  have hal216 : ((s.m.core.read .rsp).toNat - 216) % 16 = 0 := by have := hI.al; omega
  have e8 : (s.m.core.read .rsp - 8#64).toNat = (s.m.core.read .rsp).toNat - 8 :=
    sub_toNat (k := 8) (by omega) (by decide)
  have hctxN : (s.m.core.read .rsp - 184#64).toNat = (s.m.core.read .rsp).toNat - 184 :=
    sub_toNat (k := 184) (by omega) (by decide)
  have hrdx := hI.rdxhi
  have hbb := permitted_bound hI.bufr
  have hbelow : buf.toNat + 0x8048 ≤ (s.m.core.read .rsp).toNat - 1024 := by
    have := (hI.bufok (buf.toNat + 0x8047) (by omega) (by omega)).2.1; omega
  set A := x.m.core.read .rbp + BitVec.signExtend 64 0xffffff48#32 with hA
  have a1 : A.toNat = (s.m.core.read .rsp).toNat - 192 := by
    rw [hA, hI.rbp, show BitVec.signExtend 64 0xffffff48#32 = 0xffffffffffffff48#64 by decide, BitVec.toNat_add, e8]
    simp only [BitVec.toNat_ofNat]; omega
  have hcw : x.m.core.read .rbp + 18446744073709551440#64 = s.m.core.read .rsp - 184#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [hctxN, hI.rbp, BitVec.toNat_add, e8]
    simp only [BitVec.toNat_ofNat]; omega
  have a1L : (x.m.core.read .rbp + 18446744073709551432#64).toNat = (s.m.core.read .rsp).toNat - 192 := a1
  have pw : x.m.memory.Permitted .write A.toNat 8 := by
    rw [a1]; exact room_perm hB.room (Or.inr rfl) (by omega) (by omega)
  have pr : x.m.memory.Permitted .read A.toNat 8 := by
    rw [a1]; exact room_perm hB.room (Or.inl rfl) (by omega) (by omega)
  refine must_listed (o := 129) shaD_listing_ok.2.2 rfl hB.done (by rw [hrip]; exact hin _ (by decide))
    hB.mem.2.digestFile (by rw [hrip, ripadd]) ?_
  xstep [hrip]
  refine must_listed (o := 136) shaD_listing_ok.2.2 rfl hB.done (hin _ (by decide)) hB.mem.2.digestFile (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 142) shaD_listing_ok.2.2 rfl hB.done (hin _ (by decide)) hB.mem.2.digestFile (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 145) shaD_listing_ok.2.2 rfl hB.done (hin _ (by decide)) hB.mem.2.digestFile (by rw [ripadd]) ?_
  rw [exec_storeq _ _ _ _ _ _ (by
    show x.m.memory.Permitted .write (x.m.core.read .rbp + BitVec.signExtend 64 0xffffff48#32).toNat 8; exact pw), WP_ok]
  have hkS : Keeps (fun a => a < (s.m.core.read .rsp).toNat - 192 ∨ (s.m.core.read .rsp).toNat - 184 ≤ a)
      x.m.memory (storeMem x.m.memory (x.m.core.read .rbp + 18446744073709551432#64) 8 (s.m.core.read .rsp - 184#64)) := storeMem_keeps fun a ha => by rw [a1L]; omega
  refine must_gen (fun y => BodyX W (ShaMemCD b lb kb) s y 216 1024 (sv6 s) X ∧ y.m.core.rip = b + 0x6ad8#64 ∧
      y.m.memory = storeMem x.m.memory (x.m.core.read .rbp + 18446744073709551432#64) 8 (s.m.core.read .rsp - 184#64) ∧ y.g = x.g ∧
      y.m.core.read .rdi = s.m.core.read .rsp - 184#64 ∧ y.m.core.read .r13 = 0x8000#64 ∧
      (∀ r ∈ Silmaril.X86.sysv64.calleeSaved, r ≠ .r13 → y.m.core.read r = x.m.core.read r)) ?_ ?_
  · refine ⟨BodyX.store hMk hB (by decide) hsvb (a := x.m.core.read .rbp + 18446744073709551432#64) (k := 8)
      (v := s.m.core.read .rsp - 184#64) (by rw [a1L]; omega) (by rw [a1L]; omega) (by simp [hcw]) (by simp) rfl rfl,
      by simp, by simp [hcw], rfl, by simp [hcw], by simp, ?_⟩
    intro r hr hne
    simp only [Silmaril.X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact absurd rfl hne | simp
  rintro y ⟨hBy, hry, hmy, hgy, hdiy, h13y, hcsy⟩
  have hyr : (y.m.core.read .rsp).toNat = (s.m.core.read .rsp).toNat - 216 := by
    rw [hBy.rsp]; exact sub_toNat (by omega) (by decide)
  have hy8 : (y.m.core.read .rsp - 8#64).toNat = (s.m.core.read .rsp).toNat - 224 := by
    rw [sub_toNat (k := 8) (by rw [hyr]; omega) (by decide), hyr]; omega
  have hlo8 : E.S.lo ≤ (y.m.core.read .rsp - 8#64).toNat := by rw [hy8]; omega
  have hAlo : E.S.lo ≤ (x.m.core.read .rbp + 18446744073709551432#64).toNat := by rw [a1L]; omega
  -- the memory at the entry of SHA256_Init
  have hpe : ∀ a, a < E.S.lo → (pushMem y.m.memory (y.m.core.read .rsp) (b + 27200#64 + BitVec.ofNat 64 (152 + 5))).bytes.get? a
      = x.m.memory.bytes.get? a ∧ ∀ acc, (pushMem y.m.memory (y.m.core.read .rsp)
        (b + 27200#64 + BitVec.ofNat 64 (152 + 5))).permits acc a = x.m.memory.permits acc a := by
    intro a ha
    refine ⟨?_, fun acc => by rw [hmy]; rfl⟩
    rw [(pushMem_keeps (P := fun x => x < E.S.lo) (m := y.m.memory) (sp := y.m.core.read .rsp)
      (v := b + 27200#64 + BitVec.ofNat 64 (152 + 5)) (fun x hx => Or.inl (by omega)) a ha).1, hmy]
    exact (hkS a (Or.inl (by omega))).1
  have hpp : E.S.priv (pushMem y.m.memory (y.m.core.read .rsp) (b + 27200#64 + BitVec.ofNat 64 (152 + 5))) =
      E.S.priv x.m.memory := E.S.priv_local _ _ hpe
  have hpushp : ∀ a acc, (pushMem y.m.memory (y.m.core.read .rsp) (b + 27200#64 + BitVec.ofNat 64 (152 + 5))).permits
      acc a = x.m.memory.permits acc a := fun a acc => by rw [hmy]; rfl
  have hfy : E.S.file y.m.memory F st := by rw [hmy]; exact file_store hI.file hAlo
  have hothy : ∀ f st', f ≠ F → E.S.file s.m.memory f st' → E.S.file y.m.memory f st' := fun f st' hne h => by
    rw [hmy]; exact file_store (hI.others f st' hne h) hAlo
  refine body_callK (shaMemCD_keep I.cl.img I.cl.hb) hBy (by decide) (by decide) hsv hal216 I.cl.lz
    (o := 152) (so := 0xe0) (pb := b + 0x23c0#64) (fp := ctxRange (s.m.core.read .rsp - 184#64))
    shaD_listing_ok.2.2 rfl (by rw [hry]; exact hin _ (by decide)) (fun m h => h.2.digestFile)
    (by rw [hry, ripadd]) shaC_listing_ok.1 rfl rfl (by simp only [BitVec.add_assoc]; rfl)
    (img_off I.cl.img I.cl.hb (by decide)) (img_off I.cl.img I.cl.hb (by decide)) (fun m h => h.1.plt)
    (fun m h => by
      rw [show b + 0x23c0#64 + BitVec.ofNat 64 (0xe0 + 4 + 6) + BitVec.signExtend 64 0x799e#32 = b + 0x9e48#64 by
        simp only [BitVec.add_assoc]; rfl]
      exact h.2.shaInit)
    I.init.1 I.init.2.1 I.init.2.2.1 (fun r h => framed_imp ((impOk_fn I.init _ r).1 h))
    ?_ ?_ ?_ (fun x h => hI.hX x h) ?_
  · intro he
    refine ⟨⟨he, ?_⟩, ?_⟩
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
  refine must_listed (o := 157) shaD_listing_ok.2.2 rfl hBv.done (by rw [hrv]; exact img_off I.cl.img I.cl.hb (by decide))
    hBv.mem.2.digestFile (by rw [hrv, ripadd]) ?_
  xstep [hrv]
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
  have hreg : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, r ≠ .r15 → r ≠ .r13 → t.m.core.read r = x.m.core.read r :=
    fun r hr hne h13 => by rw [hcst r hr hne, hcsv r hr, hcsy r hr h13]
  obtain ⟨-, -, -, -, hpg, hperm, -⟩ := hv.2.1
  simp only [callEntry_mem, hpp] at hpg hperm
  have hini := hv.1.2.1
  simp only [callEntry_read _ _ _ (by decide : Reg.rdi ≠ .rsp), hdiy] at hini
  have hoth := hv.2.2
  unfold OthersKept at hoth; simp only [callEntry_mem] at hoth
  have hgv : v.g = x.g := by rw [hv.1.2.2.2]; simp only [callEntry_g]; exact hgy
  -- the frame outside the context
  have hk8 : ∀ a, (s.m.core.read .rsp).toNat - 216 ≤ a → a + 8 ≤ (s.m.core.read .rsp).toNat - 184 ∨
      (s.m.core.read .rsp).toNat - 72 ≤ a → v.m.memory.readBytes a 8 = y.m.memory.readBytes a 8 := by
    intro a h1 h2
    rw [hkv.readBytes (fun j hj => ⟨Or.inr (by omega), fun h => by unfold ctxRange at h; rw [hctxN] at h; omega⟩)]
  have hbmapped : ∀ a, buf.toNat ≤ a → a < buf.toNat + 0x8048 → x.m.memory.permits .read a = true := by
    intro a h1 h2
    have := hI.bufr; unfold Memory.Permitted at this; rw [Memory.checkSpan_iff] at this
    have h := this.2.2 (a - buf.toNat) (by omega); rwa [show buf.toNat + (a - buf.toNat) = a by omega] at h
  have hbperm : ∀ a, buf.toNat ≤ a → a < buf.toNat + 0x8048 → ∀ acc, v.m.memory.permits acc a = x.m.memory.permits acc a := by
    intro a h1 h2 acc
    rw [hperm a (hI.bufok a h1 h2).2.2.2 (by rw [hpushp]; exact hbmapped a h1 h2) acc, hpushp]
  have hLy : LibK E W s.m.memory y.m.memory := by
    rw [hmy]; exact hI.lib.high (storeMem_keeps fun a ha => by rw [a1L]; omega)
  have hLt : LibK E W s.m.memory t.m.memory := by
    rw [hmt]; exact hLy.call hlo8 hv.2.1 fun a ha hf => by
      simp only [callEntry_read _ _ _ (by decide : Reg.rdi ≠ .rsp), hdiy] at hf
      unfold ctxRange at hf; rw [hctxN] at hf; have := ha.1; omega
  refine k t ⟨hI.hX, hI.lo, hI.al, hBv.of_eq hmt hspt hfst (by rw [hgt]), ?_, ?_, ?_, ?_, ?_, ?_, by simp,
    ?_, ?_, ?_, ?_, hI.rdxhi, ?_, ?_, ?_, ?_, ?_, ?_, hI.stok, by simp only [List.nil_append]; exact hI.data, ?_, ?_, ?_,
    hLt, hI.buffr⟩ hrt
  · rw [hreg .rbp (by simp [Silmaril.X86.sysv64_calleeSaved]) (by decide) (by decide)]; exact hI.rbp
  · rw [hreg .rbx (by simp [Silmaril.X86.sysv64_calleeSaved]) (by decide) (by decide)]; exact hI.rbx
  · rw [hreg .r12 (by simp [Silmaril.X86.sysv64_calleeSaved]) (by decide) (by decide)]; exact hI.r12
  · rw [hcst .r13 (by simp [Silmaril.X86.sysv64_calleeSaved]) (by decide),
      hcsv .r13 (by simp [Silmaril.X86.sysv64_calleeSaved]), h13y]
  · rw [hreg .r14 (by simp [Silmaril.X86.sysv64_calleeSaved]) (by decide) (by decide)]; exact hI.r14
  · rw [h15t]; rfl
  · rw [hmt, hk8 _ (by omega) (Or.inl (by omega)), hmy, storeMem_read_ne (by rw [a1L]; omega)]; exact hI.sbin
  · have hpr : x.m.memory.Permitted .read (x.m.core.read .rbp + 18446744073709551432#64).toNat 8 := by
      rw [a1L]; exact room_perm hB.room (Or.inl rfl) (by omega) (by omega)
    rw [hmt, hk8 _ (by omega) (Or.inl (by omega)), hmy, ← a1L, storeMem_read8 hpr]
  · rw [hmt, hk8 _ (by omega) (Or.inr (by omega)), hmy, storeMem_read_ne (by rw [a1L]; omega)]; exact hI.sg
  · rw [hmt, hkv.readBytes (fun j hj => ⟨Or.inr (by omega), fun h => by
      unfold ctxRange at h; rw [hctxN] at h; omega⟩), hmy, storeMem_read_ne (by rw [a1L]; omega)]
    exact hI.miss
  · rw [hmt]; exact hini
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
  · rw [hmt]; exact hoth F st List.not_mem_nil (file_push hfy hlo8)
  · rw [hgt, hgv]; exact hI.g
  · intro f st' hne h
    rw [hmt]; exact hoth f st' List.not_mem_nil (file_push (hothy f st' hne h) hlo8)
  · rw [hmt]; exact (show PermDX s y.m.memory from (hI.pdx.regions (by rw [hmy]; rfl))).keep hkv
      fun a _ ha => ⟨Or.inr (by omega), fun h => by unfold ctxRange at h; rw [hctxN] at h; omega⟩

end Silmaril.Elf.Link.Dyn.Sha256sum
