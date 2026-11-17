module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.DigestInit

/-! # GNU `sha256sum`: `digest_file` from `*missing = false` to its read loop

`fopen_safer`, `fileno` and `posix_fadvise`, `malloc (BLOCKSIZE + 72)`, up to `0x6ac1` (`DigPre`),
where the code common with standard input starts (`dg_init`).
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

/-- The frame of `digest_file` while it opens the stream `F` and allocates the buffer. -/
structure DigFr (E : Env) (W : World) (b lb kb : Word) (X : Nat → Prop) (s u : PState) (F g : Word) (z : BitVec 32)
    (st : St) : Prop where
  hX : ∀ x, X x → x + 1024 < (s.m.core.read .rsp).toNat ∨ (s.m.core.read .rsp).toNat + 8 ≤ x
  lo : E.S.lo + 1024 ≤ (s.m.core.read .rsp).toNat
  al : (s.m.core.read .rsp).toNat % 16 = 8
  body : BodyX W (ShaMemCD b lb kb) s u 216 1024 (sv6 s) X
  rbp : u.m.core.read .rbp = s.m.core.read .rsp - 8#64
  rbx : u.m.core.read .rbx = F
  r14 : BitVec.setWidth 32 (u.m.core.read .r14) = z
  sbin : u.m.memory.readBytes ((s.m.core.read .rsp).toNat - 200) 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [s.m.core.read .rsi])
  sg : u.m.memory.readBytes ((s.m.core.read .rsp).toNat - 64) 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [g])
  miss : u.m.memory.readBytes (s.m.core.read .rdx).toNat 1 = some [0#8]
  rdxhi : (s.m.core.read .rsp).toNat + 8 ≤ (s.m.core.read .rdx).toNat
  file : E.S.file u.m.memory F st
  g : u.g = s.g
  others : ∀ f st', f ≠ F → E.S.file s.m.memory f st' → E.S.file u.m.memory f st'
  pdx : PermDX s u.m.memory
  /-- the library variables of the entry are kept -/
  lib : LibK E W s.m.memory u.m.memory

/-- The return address of a call from the frame lies above the streams. -/
theorem DigFr.lo8 {E : Env} {W : World} {b lb kb : Word} {X : Nat → Prop} {s u : PState} {F g : Word} {z : BitVec 32}
    {st : St} (h : DigFr E W b lb kb X s u F g z st) : E.S.lo ≤ (u.m.core.read .rsp - 8#64).toNat := by
  have hlo := h.lo
  have hur : (u.m.core.read .rsp).toNat = (s.m.core.read .rsp).toNat - 216 := by
    rw [h.body.rsp]; exact sub_toNat (by omega) (by decide)
  rw [sub_toNat (k := 8) (by omega) (by decide), hur]; omega

theorem DigFr.congr {E : Env} {W : World} {b lb kb : Word} {X : Nat → Prop} {s u v : PState} {F g : Word} {z : BitVec 32} {st : St}
    (h : DigFr E W b lb kb X s u F g z st) (hm : v.m.memory = u.m.memory)
    (hsp : v.m.core.read .rsp = u.m.core.read .rsp)
    (hcs : ∀ r, r = .rbp ∨ r = .rbx ∨ r = .r14 → v.m.core.read r = u.m.core.read r)
    (hf : v.m.core.fsBase = u.m.core.fsBase) (hg : v.g = u.g) : DigFr E W b lb kb X s v F g z st :=
  ⟨h.hX, h.lo, h.al, h.body.of_eq hm hsp hf (by rw [hg]),
    by rw [hcs .rbp (Or.inl rfl)]; exact h.rbp,
    by rw [hcs .rbx (Or.inr (Or.inl rfl))]; exact h.rbx,
    by rw [hcs .r14 (Or.inr (Or.inr rfl))]; exact h.r14,
    hm ▸ h.sbin, hm ▸ h.sg, hm ▸ h.miss, h.rdxhi, hm ▸ h.file, hg ▸ h.g, hm ▸ h.others, hm ▸ h.pdx, hm ▸ h.lib⟩

/-- A library call that writes nothing of the client's keeps the frame. -/
theorem DigFr.after {E : Env} {W : World} {b lb kb : Word} {X : Nat → Prop} {s u v : PState} {F g : Word} {z : BitVec 32}
    {st : St} (h : DigFr E W b lb kb X s u F g z st) {a ret : Word}
    (hBv : BodyX W (ShaMemCD b lb kb) s v 216 1024 (sv6 s) X)
    (hcs : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, v.m.core.read r = u.m.core.read r)
    (hkv : Keeps (fun x => (W.Kept x ∨ (s.m.core.read .rsp).toNat - 216 ≤ x) ∧ ¬ False) u.m.memory v.m.memory)
    (hoth : OthersKept E (callEntry u a ret) v []) (hg : v.g = u.g) (hlib : LibK E W s.m.memory v.m.memory) :
    DigFr E W b lb kb X s v F g z st := by
  have hlo := h.lo
  have hrdx := h.rdxhi
  have hur : (u.m.core.read .rsp).toNat = (s.m.core.read .rsp).toNat - 216 := by
    rw [h.body.rsp]; exact sub_toNat (by omega) (by decide)
  have hlo8 : E.S.lo ≤ (u.m.core.read .rsp - 8#64).toNat := by
    rw [sub_toNat (k := 8) (by omega) (by decide), hur]; omega
  have hk : ∀ c n, (s.m.core.read .rsp).toNat - 216 ≤ c → v.m.memory.readBytes c n = u.m.memory.readBytes c n :=
    fun c n hc => hkv.readBytes fun j hj => ⟨Or.inr (by omega), id⟩
  unfold OthersKept at hoth
  simp only [callEntry_mem] at hoth
  exact ⟨h.hX, h.lo, h.al, hBv,
    by rw [hcs .rbp (by simp [Silmaril.X86.sysv64_calleeSaved])]; exact h.rbp,
    by rw [hcs .rbx (by simp [Silmaril.X86.sysv64_calleeSaved])]; exact h.rbx,
    by rw [hcs .r14 (by simp [Silmaril.X86.sysv64_calleeSaved])]; exact h.r14,
    by rw [hk _ _ (by omega)]; exact h.sbin, by rw [hk _ _ (by omega)]; exact h.sg,
    by rw [hk _ _ (by omega)]; exact h.miss, h.rdxhi,
    hoth F st List.not_mem_nil (file_push h.file hlo8), by rw [hg]; exact h.g,
    fun f st' hne hf => hoth f st' List.not_mem_nil (file_push (h.others f st' hne hf) hlo8),
    h.pdx.keep hkv fun a _ ha => ⟨Or.inr (by omega), id⟩, hlib⟩

/-- A body does not depend on the library state of its entry. -/
theorem _root_.Silmaril.Elf.Link.Dyn.Proc.BodyX.rebase6 {W : World} {M : Memory → Prop} {s u : PState} {fr n : Nat} {X : Nat → Prop}
    (h : BodyX W M s u fr n (sv6 s) X) (G : Ghost) : BodyX W M { s with g := G } u fr n (sv6 { s with g := G }) X :=
  ⟨h.rsp, h.keepX, h.room, h.mem, h.fs, h.done, fun p hp => h.saved p hp, h.perm⟩

theorem PermDX.rebase {s : PState} {m : Memory} (h : PermDX s m) (G : Ghost) : PermDX { s with g := G } m :=
  ⟨h.pos, h.perm⟩

/-- Same, for a call that changes the library state to `G` (`malloc`): the frame is rebased on the entry
state with library state `G`. -/
theorem DigFr.afterG {E : Env} {W : World} {b lb kb : Word} {X : Nat → Prop} {s u v : PState} {F g : Word} {z : BitVec 32}
    {st : St} (h : DigFr E W b lb kb X s u F g z st) {a ret : Word}
    (hBv : BodyX W (ShaMemCD b lb kb) s v 216 1024 (sv6 s) X)
    (hcs : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, v.m.core.read r = u.m.core.read r)
    {fp : Nat → Prop} (hkv : Keeps (fun x => (W.Kept x ∨ (s.m.core.read .rsp).toNat - 216 ≤ x) ∧ ¬ fp x) u.m.memory v.m.memory)
    (hfpc : ∀ c, (s.m.core.read .rsp).toNat - 216 ≤ c → ¬ fp c)
    (hoth : OthersKept E (callEntry u a ret) v []) (G : Ghost) (hg : v.g = G) (hlib : LibK E W s.m.memory v.m.memory) :
    DigFr E W b lb kb X { s with g := G } v F g z st := by
  have hlo := h.lo
  have hrdx := h.rdxhi
  have hur : (u.m.core.read .rsp).toNat = (s.m.core.read .rsp).toNat - 216 := by
    rw [h.body.rsp]; exact sub_toNat (by omega) (by decide)
  have hlo8 : E.S.lo ≤ (u.m.core.read .rsp - 8#64).toNat := by
    rw [sub_toNat (k := 8) (by omega) (by decide), hur]; omega
  have hk : ∀ c n, (s.m.core.read .rsp).toNat - 216 ≤ c → v.m.memory.readBytes c n = u.m.memory.readBytes c n :=
    fun c n hc => hkv.readBytes fun j hj => ⟨Or.inr (by omega), hfpc _ (by omega)⟩
  unfold OthersKept at hoth
  simp only [callEntry_mem] at hoth
  exact ⟨h.hX, h.lo, h.al, hBv.rebase6 G,
    by rw [hcs .rbp (by simp [Silmaril.X86.sysv64_calleeSaved])]; exact h.rbp,
    by rw [hcs .rbx (by simp [Silmaril.X86.sysv64_calleeSaved])]; exact h.rbx,
    by rw [hcs .r14 (by simp [Silmaril.X86.sysv64_calleeSaved])]; exact h.r14,
    by rw [hk _ _ (by dsimp only at *; omega)]; exact h.sbin, by rw [hk _ _ (by dsimp only at *; omega)]; exact h.sg,
    by rw [hk _ _ (by dsimp only at *; omega)]; exact h.miss, h.rdxhi,
    hoth F st List.not_mem_nil (file_push h.file hlo8), hg,
    fun f st' hne hf => hoth f st' List.not_mem_nil (file_push (h.others f st' hne hf) hlo8),
    (h.pdx.keep hkv fun a _ ha => ⟨Or.inr (by omega), hfpc _ (by omega)⟩).rebase G, hlib⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- **From `0x6bb2` to `0x6ac1`** (common to a named file and standard input): `fileno`,
`posix_fadvise`, `malloc (BLOCKSIZE + 72)`. -/
theorem dg_setup {E : Env} {R : ShaRep} {W : World} {b lb kb : Word} (I : DigImps E R W b lb kb)
    {Q : PState → Prop} {X : Nat → Prop} {s u1 : PState} {F g : Word} {z : BitVec 32} {st : St}
    (hF1 : DigFr E W b lb kb X s u1 F g z st) (hru1 : u1.m.core.rip = b + 27570#64) (hdu1 : u1.m.core.read .rdi = F)
    (hst : st.fail = false ∧ st.err = false ∧ st.reading = true ∧ st.fd < 2 ^ 31 ∧ (st.eof = true → st.rd = []))
    (hroom : InMain s.g ∧ s.g.allocs < E.maxAllocs ∧ s.g.heap + 0x8048 ≤ E.maxHeap)
    (k : ∀ u buf, DigPre E W b lb kb X { s with g := s.g.alloc 0x8048 } u F buf g z st.rd st →
      u.m.core.rip = b + 0x6ac1#64 → MustQ W Q u) :
    MustQ W Q u1 := by
  have hin : ∀ n, n < 0xa188 → W.InImage (b + BitVec.ofNat 64 n).toNat := fun n hn => sha_in' I.cl.img I.cl.hb hn
  have hlo := hF1.lo
  have hsv := sv6_bound s
  have hal216 : ((s.m.core.read .rsp).toNat - 216) % 16 = 0 := by have := hF1.al; omega
  have hu1r : (u1.m.core.read .rsp).toNat = (s.m.core.read .rsp).toNat - 216 := by
    rw [hF1.body.rsp]; exact sub_toNat (by omega) (by decide)
  have hu18 : E.S.lo ≤ (u1.m.core.read .rsp - 8#64).toNat := by
    rw [sub_toNat (k := 8) (by omega) (by decide), hu1r]; omega
  refine body_callK (shaMemCD_keep I.cl.img I.cl.hb) hF1.body (by decide) (by decide) hsv hal216 I.cl.lz
    (o := 370) (so := 0x180) (pb := b + 0x23c0#64) (fp := fun _ => False)
    shaD_listing_ok.2.2 rfl (by rw [hru1]; exact hin _ (by decide)) (fun m h => h.2.digestFile)
    (by rw [hru1, ripadd]) shaC_listing_ok.1 rfl rfl (by simp only [BitVec.add_assoc]; rfl)
    (img_off I.cl.img I.cl.hb (by decide)) (img_off I.cl.img I.cl.hb (by decide)) (fun m h => h.1.plt)
    (fun m h => by
      rw [show b + 0x23c0#64 + BitVec.ofNat 64 (0x180 + 4 + 6) + BitVec.signExtend 64 0x794e#32 = b + 0x9e98#64 by
        simp only [BitVec.add_assoc]; rfl]
      exact h.1.fileno)
    I.cl.fileno.1 I.cl.fileno.2.1 I.cl.fileno.2.2.1 (fun r h => (impOk_fn I.cl.fileno _ r).1 h)
    (fun he => ⟨he, _, by rw [callEntry_mem, callEntry_read _ _ _ (by decide), hdu1]; exact file_push hF1.file hu18⟩)
    (fun v hv => ⟨hv.1.1, hv.1.2.2.1, by simpa [callEntry] using hv.1.2.1, by rw [hv.2.1]; exact hF1.body.done⟩)
    (fun x h => h.elim) (fun x hd => hF1.hX x hd) ?_
  intro v1 hv1 hBv1 hrv1 hspv1 hcsv1 hkv1
  have hF2 := hF1.after hBv1 hcsv1 hkv1 hv1.2.2.1 (by rw [hv1.2.1]; simp only [callEntry_g])
    (hF1.lib.call0 hu18 hv1.1)
  -- posix_fadvise (fd, 0, 0, POSIX_FADV_SEQUENTIAL)
  refine must_listed (o := 375) shaD_listing_ok.2.2 rfl hBv1.done (by rw [hrv1]; exact img_off I.cl.img I.cl.hb (by decide))
    hBv1.mem.2.digestFile (by rw [hrv1, ripadd]) ?_
  xstep [hrv1]
  refine must_listed (o := 380) shaD_listing_ok.2.2 rfl hBv1.done (hin _ (by decide)) hBv1.mem.2.digestFile (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 382) shaD_listing_ok.2.2 rfl hBv1.done (hin _ (by decide)) hBv1.mem.2.digestFile (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 384) shaD_listing_ok.2.2 rfl hBv1.done (hin _ (by decide)) hBv1.mem.2.digestFile (by rw [ripadd]) ?_
  xstep []
  refine must_gen (fun y => DigFr E W b lb kb X s y F g z st ∧ y.m.core.rip = b + 0x6bc2#64) ?_ ?_
  · refine ⟨hF2.congr rfl (by simp) ?_ rfl rfl, by simp⟩
    intro r hr
    rcases hr with rfl | rfl | rfl <;> simp
  rintro y2 ⟨hF3, hry2⟩
  refine body_callK (shaMemCD_keep I.cl.img I.cl.hb) hF3.body (by decide) (by decide) hsv hal216 I.cl.lz
    (o := 386) (so := 0x100) (pb := b + 0x23c0#64) (fp := fun _ => False)
    shaD_listing_ok.2.2 rfl (by rw [hry2]; exact hin _ (by decide)) (fun m h => h.2.digestFile)
    (by rw [hry2, ripadd]) shaC_listing_ok.1 rfl rfl (by simp only [BitVec.add_assoc]; rfl)
    (img_off I.cl.img I.cl.hb (by decide)) (img_off I.cl.img I.cl.hb (by decide)) (fun m h => h.1.plt)
    (fun m h => by
      rw [show b + 0x23c0#64 + BitVec.ofNat 64 (0x100 + 4 + 6) + BitVec.signExtend 64 0x798e#32 = b + 0x9e58#64 by
        simp only [BitVec.add_assoc]; rfl]
      exact h.2.fadvise)
    I.fadvise.1 I.fadvise.2.1 I.fadvise.2.2.1 (fun r h => (impOk_fn I.fadvise _ r).1 h)
    (fun he => he)
    (fun v hv => ⟨hv.1.1, hv.1.2.2.1, by simpa [callEntry] using hv.1.2.1, by rw [hv.2.2.1]; exact hF3.body.done⟩)
    (fun x h => h.elim) (fun x hd => hF1.hX x hd) ?_
  intro v2 hv2 hBv2 hrv2 hspv2 hcsv2 hkv2
  have hF4 := hF3.after hBv2 hcsv2 hkv2 hv2.2.2.2 (by rw [hv2.2.2.1]; simp only [callEntry_g])
    (hF3.lib.call0 hF3.lo8 hv2.1)
  -- malloc (BLOCKSIZE + 72)
  refine must_listed (o := 391) shaD_listing_ok.2.2 rfl hBv2.done (by rw [hrv2]; exact img_off I.cl.img I.cl.hb (by decide))
    hBv2.mem.2.digestFile (by rw [hrv2, ripadd]) ?_
  xstep [hrv2]
  refine must_gen (fun y => DigFr E W b lb kb X s y F g z st ∧ y.m.core.rip = b + 0x6bcc#64 ∧ y.m.core.read .rdi = 0x8048#64) ?_ ?_
  · refine ⟨hF4.congr rfl (by simp) ?_ rfl rfl, by simp, by simp⟩
    intro r hr
    rcases hr with rfl | rfl | rfl <;> simp
  rintro y3 ⟨hF5, hry3, hdy3⟩
  have hy3r : (y3.m.core.read .rsp).toNat = (s.m.core.read .rsp).toNat - 216 := by
    rw [hF5.body.rsp]; exact sub_toNat (by omega) (by decide)
  have hLc : LibK E W s.m.memory
      (callEntry y3 (lb + 710480#64) (b + 27200#64 + BitVec.ofNat 64 (396 + 5))).m.memory := by
    rw [callEntry_mem]; exact hF5.lib.push hF5.lo8
  refine body_callK (shaMemCD_keep I.cl.img I.cl.hb) hF5.body (by decide) (by decide) hsv hal216 I.cl.lz
    (o := 396) (so := 0x220) (pb := b + 0x23c0#64)
    (fp := fun x => ¬ W.Kept x ∧ x + 0x100000 < (s.m.core.read .rsp).toNat - 224)
    shaD_listing_ok.2.2 rfl (by rw [hry3]; exact hin _ (by decide)) (fun m h => h.2.digestFile)
    (by rw [hry3, ripadd]) shaC_listing_ok.1 rfl rfl (by simp only [BitVec.add_assoc]; rfl)
    (img_off I.cl.img I.cl.hb (by decide)) (img_off I.cl.img I.cl.hb (by decide)) (fun m h => h.1.plt)
    (fun m h => by
      rw [show b + 0x23c0#64 + BitVec.ofNat 64 (0x220 + 4 + 6) + BitVec.signExtend 64 0x78fe#32 = b + 0x9ee8#64 by
        simp only [BitVec.add_assoc]; rfl]
      exact h.2.malloc)
    I.malloc.1 I.malloc.2.1 I.malloc.2.2.1 (fun r h => (impOk_fn I.malloc _ r).1 h)
    (fun he => he)
    (fun v hv => ⟨⟨hv.1.1.1, hv.1.1.2.mono fun x hx => ⟨hx.1, fun hf => hx.2 (by
        rcases hv.2.2.2 with ⟨h0, -⟩ | ⟨-, -, -, -, -, -, h3⟩
        · exact absurd h0 hf.1
        · have h4 := h3 x hf.2.1 hf.2.2
          have hl5 := hF5.lo
          have e : ((callEntry y3 (lb + 710480#64) (b + 27200#64 + BitVec.ofNat 64 (396 + 5))).m.core.read .rsp).toNat =
              (s.m.core.read .rsp).toNat - 224 := by
            rw [callEntry_rsp, sub_toNat (k := 8) (by omega) (by decide), hy3r]; omega
          rw [e] at h4
          exact ⟨h4.2.1, h4.2.2.1⟩)⟩⟩,
      hv.1.2.2.1, by simpa [callEntry] using hv.1.2.1, by rw [hv.2.1]; exact hF5.body.done⟩)
    (fun x h => ⟨h.1, Or.inl (by omega)⟩) (fun x hd => hF1.hX x hd) ?_
  intro v3 hv3 hBv3 hrv3 hspv3 hcsv3 hkv3
  obtain ⟨hnz3, hal3, hhp3, hbl3, hbr3, hbw3, hblk3⟩ : v3.m.core.read .rax ≠ 0#64 ∧
      v3.g.allocs = s.g.allocs + 1 ∧ v3.g.heap = s.g.heap + 0x8048 ∧
      v3.g.blocks = ((v3.m.core.read .rax).toNat, 0x8048) :: s.g.blocks ∧
      v3.m.memory.Permitted .read (v3.m.core.read .rax).toNat 0x8048 ∧
      v3.m.memory.Permitted .write (v3.m.core.read .rax).toNat 0x8048 ∧
      ∀ a, (v3.m.core.read .rax).toNat ≤ a → a < (v3.m.core.read .rax).toNat + 0x8048 →
        ¬ E.S.priv v3.m.memory a ∧ ¬ W.Kept a ∧ a + 0x100000 < (s.m.core.read .rsp).toNat - 224 ∧ a < E.S.lo ∧
        ¬ LibV E W s.m.memory a := by
    rcases hv3.2.2.2 with ⟨-, ha, -⟩ | ⟨h0, hal, hhp, hbl, h1, h2, h3⟩
    · exfalso
      rcases ha with ha | ha
      · rw [I.alloc] at ha; cases ha
      · apply ha
        refine ⟨by simp only [callEntry_g]; rw [hF5.g]; exact hroom.1, ?_, by simp only [callEntry_g]; rw [hF5.g]; exact hroom.2.1, ?_⟩
        · simp only [callEntry_rsp]
          rw [sub_toNat (k := 8) (by omega) (by decide), hy3r]; have := hF5.lo; omega
        · simp only [callEntry_g, callEntry_read _ _ _ (by decide : Reg.rdi ≠ .rsp), hdy3]; rw [hF5.g]
          exact hroom.2.2
    · simp only [callEntry_g, callEntry_read _ _ _ (by decide : Reg.rdi ≠ .rsp), hdy3, callEntry_rsp] at h1 h2 h3 hal hhp hbl
      rw [hF5.g] at hal hhp hbl
      have e : (y3.m.core.read .rsp - 8#64).toNat = (s.m.core.read .rsp).toNat - 224 := by
        rw [sub_toNat (k := 8) (by omega) (by decide), hy3r]; omega
      rw [e] at h3
      exact ⟨h0, hal, by simpa using hhp, by simpa using hbl, h1, h2, fun a ha1 ha2 => ⟨(h3 a ha1 ha2).1, (h3 a ha1 ha2).2.1,
        (h3 a ha1 ha2).2.2.1, (h3 a ha1 ha2).2.2.2.1, hLc.fresh (h3 a ha1 ha2).2.2.2.2⟩⟩
  have hgv3 : v3.g = (s.g.alloc 0x8048).withBlk (v3.m.core.read .rax).toNat 0x8048 := by
    rw [hv3.2.1, hal3, hhp3, hbl3]; simp only [callEntry_g]; rw [hF5.g]; rfl
  have hF6 := hF5.afterG hBv3 hcsv3 hkv3 (fun c hc h => by omega) hv3.2.2.1 _ hgv3
    (hLc.libRet hv3.1 fun a ha hf => by
      rw [callEntry_read _ _ _ (by decide : Reg.rdi ≠ .rsp), hdy3] at hf
      exact (hblk3 a hf.2.1 hf.2.2).2.2.2.2 ha)
  refine must_listed (o := 401) shaD_listing_ok.2.2 rfl hBv3.done (by rw [hrv3]; exact img_off I.cl.img I.cl.hb (by decide))
    hBv3.mem.2.digestFile (by rw [hrv3, ripadd]) ?_
  xstep [hrv3]
  refine must_listed (o := 404) shaD_listing_ok.2.2 rfl hBv3.done (hin _ (by decide)) hBv3.mem.2.digestFile (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 407) shaD_listing_ok.2.2 rfl hBv3.done (hin _ (by decide)) hBv3.mem.2.digestFile (by rw [ripadd]) ?_
  xstep [eval_ne_testQ, hnz3]
  refine must_gen (fun y => DigFr E W b lb kb X { s with g := (s.g.alloc 0x8048).withBlk (v3.m.core.read .rax).toNat 0x8048 } y F g z st ∧
      y.m.core.rip = b + 0x6ac1#64 ∧ y.m.core.read .r12 = v3.m.core.read .rax ∧
      y.m.memory = v3.m.memory) ?_ ?_
  · refine ⟨hF6.congr rfl (by simp) ?_ rfl rfl, by simp, by simp, rfl⟩
    intro r hr
    rcases hr with rfl | rfl | rfl <;> simp
  rintro y4 ⟨hF7, hry4, h12y4, hmy4⟩
  refine k y4 _ ⟨hF7.hX, hF7.lo, hF7.al, hF7.body.rebase6 _, hF7.rbp, hF7.rbx, h12y4, hF7.r14, hF7.sbin, hF7.sg,
    hF7.miss, hF7.rdxhi, by rw [hmy4]; exact hbr3, by rw [hmy4]; exact hbw3, ?_, hF7.file,
    hst, rfl, by rw [hF7.g], hF7.others, hF7.pdx.rebase _, hF7.lib, fun a h1 h2 => (hblk3 a h1 h2).2.2.2.2⟩ hry4
  intro a h1 h2
  have := hblk3 a h1 h2
  exact ⟨this.2.1, by dsimp only at *; omega, this.2.2.2.1, by rw [hmy4]; exact this.1⟩


set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- **`digest_file` from `*missing = false` to the read loop.** -/
theorem sha_digest_head {E : Env} {R : ShaRep} {W : World} {b lb kb : Word} (I : DigImps E R W b lb kb)
    {Q : PState → Prop} {s x : PState} {g : Word} (hM : DigMid E W b lb kb s x g)
    (hrx : x.m.core.rip = b + 0x6a88#64) (h14x : BitVec.setWidth 32 (x.m.core.read .r14) ≠ 0#32)
    (hlo : E.S.lo + 1024 ≤ (s.m.core.read .rsp).toNat) (hal : (s.m.core.read .rsp).toNat % 16 = 8)
    {p : List Byte} (hp : CStr s.m.memory (s.m.core.read .rdi) p)
    (hpk : ∀ j, j < p.length + 1 → W.Kept ((s.m.core.read .rdi).toNat + j))
    {data : Silmaril.Apps.Sha256sum.Bytes} (hfs : E.fs (toSpec p) = .ok data)
    (hX : ∀ a, DX s a → ¬ W.Kept a ∧ (s.m.core.read .rsp).toNat + 8 ≤ a)
    (hres : InMain s.g ∧ s.g.files < E.maxOpen ∧ data.length ≤ E.maxFile ∧ s.g.allocs < E.maxAllocs ∧
      s.g.heap + 0x8048 ≤ E.maxHeap)
    (k : ∀ u F buf (fd : Nat), DigPre E W b lb kb (MX s) { s with g := s.g.opened.alloc 0x8048 } u F buf g
      (BitVec.setWidth 32 (x.m.core.read .r14))
      (ofSpec data) (openSt data fd) → u.m.core.rip = b + 0x6ac1#64 → 3 ≤ fd →
      (∀ st0, ¬ E.S.file s.m.memory F st0) → MustQ W Q u) :
    MustQ W Q x := by
  have hin : ∀ n, n < 0xa188 → W.InImage (b + BitVec.ofNat 64 n).toNat := fun n hn => sha_in' I.cl.img I.cl.hb hn
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
  refine sha_fopenSafer I.cl I.fopen (p := p) (data := data) rfl
    (abiEntry_of (v := b + 27555#64) (by show (x.m.core.read .rsp - 8#64).toNat % 16 = 8; rw [hx8]; omega)
      (by simpa using pushMem_read pr pw))
    (by simpa using hroom1) (by show E.S.lo + 256 ≤ (x.m.core.read .rsp - 8#64).toNat; rw [hx8]; omega) hB.done
    (hMk _ _ hB.mem (hpush.mono fun a ha => Or.inl (Or.inl ha))) (by simpa using hp1) (by simpa using hpk) hfs I.alloc
    (by show InMain x.g ∧ x.g.files < _ ∧ _; rw [hM.g]; exact ⟨hres.1, hres.2.1, hres.2.2.1⟩) ?_
  intro t fd habiT hkT hgT hfT hfd3 hfd31 hnz hnewT hokT hfsT hPT hLT
  have hLt : LibK E W s.m.memory t.m.memory :=
    (((LibK.refl E W s.m.memory).high hM.low).push (v := b + 27555#64) (by rw [hx8]; omega)).trans hLT
  obtain ⟨hB1, hrip1, hrsp1, hcs1⟩ := body_after (shaMemCD_keep I.cl.img I.cl.hb) hB (by decide) (by decide)
    (sv6_bound s) (ret := b + 27555#64)
    (hpost := ⟨⟨habiT, hkT.mono fun a ha => ha.1⟩, halfOfKeep hkT hPT, by rw [hgT]; exact hB.done⟩)
    (hem := by exact rfl) (hersp := by simp)
    (hecs := by
      intro r hr
      simp only [Silmaril.X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
    (hefs := by exact rfl) (hvfs := hfsT) (hfp := fun x (h : False) => h.elim) (hX := fun x hd => Or.inr (hX x (Or.inl hd)).2)
  -- the frame's facts carried across the call
  have hkF : Keeps (fun a => (s.m.core.read .rsp).toNat - 216 ≤ a ∧ a < (s.m.core.read .rsp).toNat) x.m.memory t.m.memory :=
    (hpush.mono fun a ha => Or.inr ha.1).trans (hkT.mono fun a ha => Or.inr (by
      show (x.m.core.read .rsp - 8#64).toNat ≤ a; rw [hx8]; omega))
  have hFx : ∀ f st', E.S.file s.m.memory f st' → E.S.file x.m.memory f st' := fun f st' h =>
    (E.S.local_ _ _ _ _ (fun a ha => hM.low a (E.S.foot_lo _ _ _ _ h ha)) h).1
  have hFt : ∀ f st', E.S.file s.m.memory f st' → E.S.file t.m.memory f st' := fun f st' h =>
    hokT f st' (by simpa using file_push (v := b + 27555#64) (hFx f st' h) (by rw [hx8]; omega))
  have hgt : t.g = s.g.opened := by rw [hgT]; simp only; rw [hM.g]
  have hcs : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, t.m.core.read r = x.m.core.read r := hcs1
  have hza : Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.logicFlagsN (andQ (t.m.core.read .rax) (t.m.core.read .rax)))
      .e = some false := by rw [eval_e_testQ]; simp [hnz]
  refine must_listed (o := 355) shaD_listing_ok.2.2 rfl hB1.done (by rw [hrip1]; exact hin _ (by decide))
    hB1.mem.2.digestFile (by rw [hrip1, ripadd]) ?_
  xstep [hrip1]
  refine must_listed (o := 358) shaD_listing_ok.2.2 rfl hB1.done (hin _ (by decide)) hB1.mem.2.digestFile (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 361) shaD_listing_ok.2.2 rfl hB1.done (hin _ (by decide)) hB1.mem.2.digestFile (by rw [ripadd]) ?_
  xstep [hza]
  refine must_listed (o := 367) shaD_listing_ok.2.2 rfl hB1.done (hin _ (by decide)) hB1.mem.2.digestFile (by rw [ripadd]) ?_
  xstep []
  have hsv := sv6_bound s
  have hal216 : ((s.m.core.read .rsp).toNat - 216) % 16 = 0 := by omega
  have hFt8 : E.S.lo ≤ (t.m.core.read .rsp - 8#64).toNat := by rw [hrsp1, hx8]; omega
  -- fileno (F)
  refine must_gen (fun u => BodyX W (ShaMemCD b lb kb) s u 216 1024 (sv6 s) (MX s) ∧ u.m.core.rip = b + 27570#64 ∧
      u.m.core.read .rdi = t.m.core.read .rax ∧ u.m.memory = t.m.memory ∧ u.m.core.read .rsp = t.m.core.read .rsp ∧
      u.g = t.g ∧ (∀ r ∈ Silmaril.X86.sysv64.calleeSaved, r ≠ .rbx → u.m.core.read r = t.m.core.read r) ∧
      u.m.core.read .rbx = t.m.core.read .rax) ?_ ?_
  · refine ⟨hB1.of_eq rfl (by simp) rfl rfl, rfl, by simp, rfl, by simp, rfl, ?_, by simp⟩
    intro r hr hne
    simp only [Silmaril.X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact absurd rfl hne | simp
  rintro u1 ⟨hBu1, hru1, hdu1, hmu1, hspu1, hgu1, hcsu1, hbxu1⟩
  have hfF1 : E.S.file u1.m.memory (t.m.core.read .rax) (openSt data fd) := by rw [hmu1]; exact hfT
  have hu18 : E.S.lo ≤ (u1.m.core.read .rsp - 8#64).toNat := by rw [hspu1]; exact hFt8
  have hkF' : Keeps (fun a => (s.m.core.read .rsp).toNat - 216 ≤ a) x.m.memory t.m.memory :=
    (hpush.mono fun a ha => Or.inr ha).trans (hkT.mono fun a ha => Or.inr (by
      show (x.m.core.read .rsp - 8#64).toNat ≤ a; rw [hx8]; omega))
  have hrdx : (s.m.core.read .rsp).toNat + 8 ≤ (s.m.core.read .rdx).toNat :=
    (hX _ (Or.inl ⟨le_refl _, by omega⟩)).2
  have hcsu : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, r ≠ .rbx → u1.m.core.read r = x.m.core.read r :=
    fun r hr hne => by rw [hcsu1 r hr hne, hcs r hr]
  have hF1 : DigFr E W b lb kb (MX s) { s with g := s.g.opened } u1 (t.m.core.read .rax) g
      (BitVec.setWidth 32 (x.m.core.read .r14)) (openSt data fd) :=
    ⟨fun a h => Or.inr (hX a (Or.inl h)).2, hlo, hal, hBu1.rebase6 _,
      by rw [hcsu .rbp (by simp [Silmaril.X86.sysv64_calleeSaved]) (by decide)]; exact hM.rbp, hbxu1,
      by rw [hcsu .r14 (by simp [Silmaril.X86.sysv64_calleeSaved]) (by decide)],
      by rw [hmu1, hkF'.readBytes (fun j hj => by dsimp only at *; omega)]; exact hM.slot2,
      by rw [hmu1, hkF'.readBytes (fun j hj => by dsimp only at *; omega)]; exact hM.slot3,
      by rw [hmu1, hkF'.readBytes (fun j hj => by dsimp only at *; omega)]; exact hM.miss, hrdx, hfF1,
      by rw [hgu1, hgt], fun f st' _ h => by rw [hmu1]; exact hFt f st' h,
      ⟨fun a h => (hX a h).2, fun a h acc => by
        rw [hmu1, (hkF' a (by have := (hX a h).2; omega)).2 acc]; unfold Memory.permits; rw [hM.regs]⟩,
      hLt.of_eq hmu1⟩
  exact dg_setup I hF1 hru1 (by rw [hdu1]) ⟨rfl, rfl, rfl, hfd31, fun h => by cases h⟩
    ⟨hres.1, hres.2.2.2.1, hres.2.2.2.2⟩
    (fun v buf hP hrv => k v _ buf fd hP hrv hfd3 (fun st0 h =>
      hnewT st0 (by simpa using file_push (v := b + 27555#64) (hFx _ st0 h) (by rw [hx8]; omega))))

end Silmaril.Elf.Link.Dyn.Sha256sum
