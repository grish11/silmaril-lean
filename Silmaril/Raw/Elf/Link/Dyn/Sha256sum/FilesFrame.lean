module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.DigestEpi
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.FilesQuote

/-! # GNU `sha256sum`: frame tools for `digest_file`'s error path

* `ShaMemK`: the image facts of the error path (the GOT slots of `__errno_location` and
  `error`, the format `"%s"`, gnulib's `ignore_missing` flag clear), and `shaMemK_of_loaded`;
* `ShaMemC.keepQ`, `ShaMemD.keepQ`, `ShaMemK.keepQ`: the image facts survive a write to
  `slot0` (they are about the image below `0xa060` and the flag at `0xa171`);
* `body_afterK`: `body_after` for a local callee that also writes objects of the image
  (`fp` inside the function's written objects `X`), here `quotef` writing `slot0`;
* `dg_epiR`: `digest_file`'s return from `0x6b66` with any `eax` (the error path returns
  false).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Link (Blob)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.X86.FnContract (AbiEntry AbiReturn)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Streams
open Silmaril.Elf.Link.Dyn.Hello (abiEntry_of retOf_of)
open Silmaril.Elf.Link.Dyn (addr_toNat plainOk slotOk)

/-- The image facts of `digest_file`'s error path. -/
structure ShaMemK (b lb : Word) (mem : Memory) : Prop where
  errnoG : loadN mem (b + 0x9de8#64) 8 = some (lb + 0x2a6e0#64)
  errorG : loadN mem (b + 0x9f40#64) 8 = some (lb + 0x11e6c0#64)
  fmtS : mem.readBytes (b + 0x70fa#64).toNat 3 = some [0x25#8, 0x73#8, 0#8]
  ignore : mem.readBytes (b + 0xa171#64).toNat 1 = some [0#8]

theorem shaK_plain :
    plainOk shaFile shaRoPh shaSlots 0x70fa [0x25#8, 0x73#8, 0#8] = true ∧
    plainOk shaFile shaRwPh shaSlots 0xa171 [0#8] = true := by decide +kernel

theorem shaK_slotsOk : slotOk shaSlots 0x9de8 (.addr 2 0x2a6e0) = true ∧
    slotOk shaSlots 0x9f40 (.addr 2 0x11e6c0) = true := by decide +kernel

set_option maxRecDepth 20000 in
theorem shaMemK_of_loaded {Fk Fc Fl : Blob} (hk : ChunksOf Fk cryptoChunks) (hc : ChunksOf Fc libcChunks)
    (hl : ChunksOf Fl ldChunks) {b kb lb ldb res : Word} {ifn : Word → Option Word} {mem : Memory}
    (h : ExeLoaded [shaFile, Fk, Fc, Fl] [b, kb, lb, ldb] ifn false res mem) : ShaMemK b lb mem := by
  obtain ⟨f, b', i, D, T, hf, hb, hi, -, hD, hT, himg⟩ := h
  simp only [List.head?_cons, Option.some.injEq] at hf hb
  subst hf hb
  rw [sha_info_f, Option.some.injEq] at hi
  subst hi
  rw [sha_slots hk hc hl, Option.some.injEq] at hD
  subst hD
  have hro : shaRoPh ∈ shaInfo.phs := by decide
  have hrw : shaRwPh ∈ shaInfo.phs := by decide
  obtain ⟨p1, p2⟩ := shaK_plain
  obtain ⟨s1, s2⟩ := shaK_slotsOk
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s1 (by rfl)
  · exact himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s2 (by rfl)
  · exact himg.readPlain (l := [0x25#8, 0x73#8, 0#8]) hT hro rfl (by decide) (by decide) (by decide)
      (acc := .read) rfl p1
  · exact himg.readPlain (l := [0#8]) hT hrw rfl (by decide) (by decide) (by decide) (acc := .read) rfl p2

/-- The image outside `slot0`. -/
def ImgQ (b : Word) (a : Nat) : Prop := ShaImg b a ∧ ¬ Slot0 b a

theorem ShaMemK.keepQ {b lb : Word} (hb : b.toNat + 0xa188 < 2 ^ 64) {m m' : Memory}
    (hm : ShaMemK b lb m) (h : Keeps (ImgQ b) m m') : ShaMemK b lb m' := by
  obtain ⟨h1, h2, h3, h4⟩ := hm
  have hl : ∀ {off : Nat}, off + 8 ≤ 0xa060 → loadN m' (b + BitVec.ofNat 64 off) 8 =
      loadN m (b + BitVec.ofNat 64 off) 8 := by
    intro off ho
    simp only [loadN, Memory.readBytes]
    rw [skeeps_range hb h (by omega) (fun k hk => ⟨⟨by omega, by omega⟩, by unfold Slot0; omega⟩)]
  refine ⟨(hl (off := 0x9de8) (by decide)).trans h1, (hl (off := 0x9f40) (by decide)).trans h2, ?_, ?_⟩
  · unfold Memory.readBytes at h3 ⊢
    rw [skeeps_range (off := 0x70fa) hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, by unfold Slot0; omega⟩)]
    exact h3
  · unfold Memory.readBytes at h4 ⊢
    rw [skeeps_range (off := 0xa171) hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, by unfold Slot0; omega⟩)]
    exact h4

theorem ShaMemK.keep {b lb : Word} (hb : b.toNat + 0xa188 < 2 ^ 64) {m m' : Memory}
    (hm : ShaMemK b lb m) (h : Keeps (ShaImg b) m m') : ShaMemK b lb m' :=
  hm.keepQ hb (h.mono fun _ ha => ha.1)

theorem ShaMemC.keepQ {b lb : Word} (hb : b.toNat + 0xa188 < 2 ^ 64) {m m' : Memory}
    (hm : ShaMemC b lb m) (h : Keeps (ImgQ b) m m') : ShaMemC b lb m' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hm
  obtain ⟨l1, l2, l3, l4⟩ := shaC_lens
  have hl : ∀ {off : Nat}, off + 8 ≤ 0xa060 → loadN m' (b + BitVec.ofNat 64 off) 8 =
      loadN m (b + BitVec.ofNat 64 off) 8 := by
    intro off ho
    simp only [loadN, Memory.readBytes]
    rw [skeeps_range hb h (by omega) (fun k hk => ⟨⟨by omega, by omega⟩, by unfold Slot0; omega⟩)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Loaded Memory.fetchBytes at h1 ⊢
    rw [l1] at h1 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, by unfold Slot0; omega⟩)]; exact h1
  · unfold Loaded Memory.fetchBytes at h2 ⊢
    rw [l2] at h2 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, by unfold Slot0; omega⟩)]; exact h2
  · unfold Loaded Memory.fetchBytes at h3 ⊢
    rw [l3] at h3 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, by unfold Slot0; omega⟩)]; exact h3
  · unfold Loaded Memory.fetchBytes at h4 ⊢
    rw [l4] at h4 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, by unfold Slot0; omega⟩)]; exact h4
  · exact (hl (off := 0x9f00) (by decide)).trans h5
  · exact (hl (off := 0x9e98) (by decide)).trans h6
  · exact (hl (off := 0x9e60) (by decide)).trans h7
  · exact (hl (off := 0x9f58) (by decide)).trans h8
  · exact (hl (off := 0x9ec8) (by decide)).trans h9
  · exact (hl (off := 0x9e88) (by decide)).trans h10
  · exact (hl (off := 0x9f98) (by decide)).trans h11
  · exact (hl (off := 0x9fc0) (by decide)).trans h12

theorem ShaMemD.keepQ {b lb kb : Word} (hb : b.toNat + 0xa188 < 2 ^ 64) {m m' : Memory}
    (hm : ShaMemD b lb kb m) (h : Keeps (ImgQ b) m m') : ShaMemD b lb kb m' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hm
  obtain ⟨l1, l2, l3⟩ := shaD_lens
  have hl : ∀ {off : Nat}, off + 8 ≤ 0xa060 → loadN m' (b + BitVec.ofNat 64 off) 8 =
      loadN m (b + BitVec.ofNat 64 off) 8 := by
    intro off ho
    simp only [loadN, Memory.readBytes]
    rw [skeeps_range hb h (by omega) (fun k hk => ⟨⟨by omega, by omega⟩, by unfold Slot0; omega⟩)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Loaded Memory.fetchBytes at h1 ⊢
    rw [l1] at h1 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, by unfold Slot0; omega⟩)]; exact h1
  · unfold Loaded Memory.fetchBytes at h2 ⊢
    rw [l2] at h2 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, by unfold Slot0; omega⟩)]; exact h2
  · unfold Loaded Memory.fetchBytes at h3 ⊢
    rw [l3] at h3 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, by unfold Slot0; omega⟩)]; exact h3
  · unfold Memory.readBytes at h4 ⊢
    rw [skeeps_range (off := 0x70bd) hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, by unfold Slot0; omega⟩)]; exact h4
  · exact (hl (off := 0x9ed0) (by decide)).trans h5
  · exact (hl (off := 0x9e58) (by decide)).trans h6
  · exact (hl (off := 0x9ee8) (by decide)).trans h7
  · exact (hl (off := 0x9ed8) (by decide)).trans h8
  · exact (hl (off := 0x9f60) (by decide)).trans h9
  · exact (hl (off := 0x9e48) (by decide)).trans h10
  · exact (hl (off := 0x9f50) (by decide)).trans h11
  · exact (hl (off := 0x9f90) (by decide)).trans h12


set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **After a local call whose callee also writes objects `fp` of the image** that the function
writes for its caller (`fp ⊆ X` there): `body_after` with the image kept outside `fp`. -/
theorem body_afterK {W : World} {M : Memory → Prop} {fp : Nat → Prop}
    (hM : ∀ m m', M m → Keeps (fun x => W.InImage x ∧ ¬ fp x) m m' → M m') {s u e v : PState} {fr n sv : Nat}
    {saved : List (Nat × Word)} {X : Nat → Prop} (hB : BodyX W M s u fr n saved X)
    (hfr : fr + 8 ≤ n) (hn : n + 16 ≤ 0x80000) (hsv : ∀ p ∈ saved, p.1 ≤ sv ∧ sv ≤ fr) {ret : Word}
    (hem : e.m.memory = pushMem u.m.memory (u.m.core.read .rsp) ret)
    (hersp : e.m.core.read .rsp = u.m.core.read .rsp - 8#64)
    (hecs : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, e.m.core.read r = u.m.core.read r)
    (hefs : e.m.core.fsBase = u.m.core.fsBase)
    (hpost : Imports.ReturnsExcept W fp e v ∧ HalfPerm e v ∧ v.g.done = none)
    (hvfs : v.m.core.fsBase = e.m.core.fsBase)
    (hfp : ∀ x, fp x → X x ∨ (¬ W.Kept x ∧ x + sv < (s.m.core.read .rsp).toNat))
    (hX : ∀ x, X x → x + n < (s.m.core.read .rsp).toNat ∨ (s.m.core.read .rsp).toNat + 8 ≤ x) :
    BodyX W M s v fr n saved X ∧ v.m.core.rip = ret ∧ v.m.core.read .rsp = u.m.core.read .rsp ∧
      (∀ r ∈ Silmaril.X86.sysv64.calleeSaved, v.m.core.read r = u.m.core.read r) := by
  obtain ⟨hrsp, hkeep, hroom, hmem, hfs, hdn, hsaved, hperm⟩ := hB
  have hn1 := hroom.1
  have hn2 := hroom.2.1
  have eu : (u.m.core.read .rsp).toNat = (s.m.core.read .rsp).toNat - fr := by
    rw [hrsp]; exact sub_toNat (by omega) (by omega)
  have eu8 : (u.m.core.read .rsp - 8#64).toNat = (s.m.core.read .rsp).toNat - fr - 8 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), eu]
  have hpw : u.m.memory.Permitted .write (u.m.core.read .rsp - 8#64).toNat 8 :=
    room_perm hroom (Or.inr rfl) (by omega) (by omega)
  have hpr : u.m.memory.Permitted .read (u.m.core.read .rsp - 8#64).toNat 8 :=
    room_perm hroom (Or.inl rfl) (by omega) (by omega)
  have hkp : Keeps (fun x => x < (s.m.core.read .rsp).toNat - fr - 8 ∨ (s.m.core.read .rsp).toNat - fr ≤ x)
      u.m.memory (pushMem u.m.memory (u.m.core.read .rsp) ret) :=
    pushMem_keeps fun x hx => by rw [eu8]; omega
  have hret := pushMem_read (v := ret) hpr hpw
  obtain ⟨⟨habi, hk⟩, hsp, hdn'⟩ := hpost
  have hcsp : (e.m.core.read .rsp).toNat = (s.m.core.read .rsp).toNat - fr - 8 := by rw [hersp]; exact eu8
  rw [hem] at hk habi
  have hkv : Keeps (fun x => (W.Kept x ∨ (s.m.core.read .rsp).toNat - fr ≤ x) ∧ ¬ fp x) u.m.memory v.m.memory := by
    refine (hkp.mono fun x hx => ?_).trans (hk.mono fun x hx => ⟨?_, hx.2⟩)
    · rcases hx.1 with h | h
      · by_cases hc : (s.m.core.read .rsp).toNat - n ≤ x ∧ x < (s.m.core.read .rsp).toNat + 8
        · exact absurd h (hroom.2.2 x hc.1 hc.2).2.2
        · omega
      · omega
    · rcases hx.1 with h | h
      · exact Or.inl h
      · right; rw [hcsp]; omega
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, hdn', ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [habi.stack, hersp, BitVec.sub_add_cancel, hrsp]
  · refine hkeep.trans (hkv.mono fun x hx => ⟨?_, fun hf => ?_⟩)
    · rcases hx.1 with h | h
      · exact Or.inl h
      · right; omega
    · rcases hfp x hf with h' | ⟨h1, h2⟩
      · exact hx.2 h'
      · rcases hx.1 with h | h
        · exact h1 h
        · omega
  · refine hroom.keeps fun x h1 h2 acc => ?_
    have r1 : (s.m.core.read .rsp).toNat - 0x80000 ≤ x := Nat.le_trans (Nat.sub_le_sub_left (by omega) _) h1
    obtain ⟨q1, q2⟩ := range_in2 hcsp r1 h2 (by omega) (by omega)
    have e1 := hsp x q1 q2 acc
    rw [e1, hem]; rfl
  · exact hM _ _ hmem (hkv.mono fun x hx => ⟨Or.inl (Or.inl hx.1), hx.2⟩)
  · rw [hvfs, hefs, hfs]
  · intro p hp
    obtain ⟨h1, h2⟩ := hsv p hp
    rw [hkv.readBytes (fun j hj => ⟨Or.inr (by omega), fun hf => by
      rcases hfp _ hf with h' | ⟨-, h'⟩
      · rcases hX _ h' with h'' | h'' <;> omega
      · omega⟩)]
    exact hsaved p hp
  · intro x h1 h2 acc
    obtain ⟨q1, q2⟩ := range_in2 hcsp h1 h2 (by omega) (by omega)
    rw [hsp x q1 q2 acc, hem]; exact hperm x h1 h2 acc
  · rw [habi.pc]; exact retOf_of (by rw [hersp]; exact hret)
  · rw [habi.stack, hersp, BitVec.sub_add_cancel]
  · intro r hr
    rw [habi.calleeSaved r hr, hecs r hr]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- **`digest_file` returns** from `0x6b66` with the `eax` it has (the error path's `false`): the
guard intact, the six saved registers restored. -/
theorem dg_epiR {E : Env} {W : World} {b lb kb : Word} (I : CloseImps E W b lb)
    {X : Nat → Prop} {Q : PState → Prop} {s u : PState} {g : Word}
    {M : Memory → Prop} (hMD : ∀ m, M m → ShaMemCD b lb kb m)
    (hB : BodyX W M s u 216 1024 (sv6 s) X) (hrip : u.m.core.rip = b + 0x6b66#64)
    (hrbp : u.m.core.read .rbp = s.m.core.read .rsp - 8#64)
    (hsg : u.m.memory.readBytes ((s.m.core.read .rsp).toNat - 64) 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [g]))
    (habi : AbiEntry s.m.core s.m.memory)
    (hguard : loadN s.m.memory (s.m.core.fsBase + 0x28#64) 8 = some g)
    (hgk : ∀ j, j < 8 → W.Kept ((s.m.core.fsBase + 0x28#64).toNat + j))
    (hXg : ∀ j, j < 8 → ¬ X ((s.m.core.fsBase + 0x28#64).toNat + j))
    (hXr : ∀ j, j < 8 → ¬ X ((s.m.core.read .rsp).toNat + j))
    (k : ∀ t, AbiReturn s.m.core s.m.memory t.m.core → t.m.memory = u.m.memory → t.m.core.read .rax = u.m.core.read .rax →
      t.g = u.g → t.m.core.fsBase = s.m.core.fsBase → MustQ W Q t) :
    MustQ W Q u := by
  have hin : ∀ n, n < 0xa188 → W.InImage (b + BitVec.ofNat 64 n).toNat := fun n hn => sha_in' I.img I.hb hn
  have hroom := hB.room
  have hsp := hroom.1
  have hsp2 := hroom.2.1
  have e8 : (s.m.core.read .rsp - 8#64).toNat = (s.m.core.read .rsp).toNat - 8 :=
    sub_toNat (k := 8) (by omega) (by decide)
  have hur : (u.m.core.read .rsp).toNat = (s.m.core.read .rsp).toNat - 216 := by
    rw [hB.rsp]; exact sub_toNat (by omega) (by decide)
  have a64 : (u.m.core.read .rbp + BitVec.signExtend 64 0xffffffc8#32).toNat = (s.m.core.read .rsp).toNat - 64 := by
    rw [hrbp, show BitVec.signExtend 64 0xffffffc8#32 = 0xffffffffffffffc8#64 by decide, BitVec.toNat_add, e8]
    simp only [BitVec.toNat_ofNat]; omega
  have hgu : loadN u.m.memory (u.m.core.fsBase + BitVec.signExtend 64 0x28#32) 8 = some g := by
    rw [hB.fs, show BitVec.signExtend 64 0x28#32 = 0x28#64 by decide,
      hB.keepX.loadN (fun j hj => ⟨Or.inl (hgk j hj), hXg j hj⟩)]
    exact hguard
  have hDF := (hMD _ hB.mem).2.digestFile
  refine must_listed (o := 294) shaD_listing_ok.2.2 rfl hB.done (by rw [hrip]; exact hin _ (by decide))
    hDF (by rw [hrip, ripadd]) ?_
  rw [exec_loadqd _ _ _ _ _ _ _ (by
    show loadN u.m.memory (u.m.core.read .rbp + BitVec.signExtend 64 0xffffffc8#32) 8 = some g
    exact loadN_of_enc (by rw [a64]; exact hsg)), WP_ok]
  refine must_listed (o := 298) shaD_listing_ok.2.2 rfl hB.done (by simp only [hrip, ripadd]; exact hin _ (by decide))
    hDF (by simp only [hrip, ripadd]) ?_
  rw [exec_subfs _ _ _ _ _ g (by show loadN u.m.memory (u.m.core.fsBase + BitVec.signExtend 64 0x28#32) 8 = some g; exact hgu),
    WP_ok]
  refine must_listed (o := 307) shaD_listing_ok.2.2 rfl hB.done (by simp only [hrip, ripadd]; exact hin _ (by decide))
    hDF (by simp only [hrip, ripadd]) ?_
  have hne : Silmaril.X86.Ext.Cond.afterCmp (w := 63) g g .ne = false := by
    simp [Silmaril.X86.Ext.Cond.afterCmp]
  xstep [eval_subQ, hrip, hne]
  refine must_listed (o := 313) shaD_listing_ok.2.2 rfl hB.done (hin _ (by decide)) hDF (by rw [ripadd]) ?_
  xstep []
  have sv : ∀ p ∈ sv6 s, u.m.memory.readBytes ((s.m.core.read .rsp).toNat - p.1) 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [p.2]) := hB.saved
  have sv1 := sv (48, s.m.core.read .rbx) (by simp [sv6])
  have sv2 := sv (40, s.m.core.read .r12) (by simp [sv6])
  have sv3 := sv (32, s.m.core.read .r13) (by simp [sv6])
  have sv4 := sv (24, s.m.core.read .r14) (by simp [sv6])
  have sv5 := sv (16, s.m.core.read .r15) (by simp [sv6])
  have sv7 := sv (8, s.m.core.read .rbp) (by simp [sv6])
  simp only at sv1 sv2 sv3 sv4 sv5 sv7
  have hret : u.m.memory.readBytes (s.m.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [Silmaril.X86.FnContract.retOf s.m.core s.m.memory]) := by
    rw [hB.keepX.readBytes (fun j hj => ⟨Or.inr (by omega), hXr j hj⟩)]
    exact habi.returnAddress
  have q1 : ((u.m.core.read .rsp).toNat + 168) % 18446744073709551616 = (s.m.core.read .rsp).toNat - 48 := by
    rw [hur]; omega
  have q2 : ((u.m.core.read .rsp).toNat + 176) % 18446744073709551616 = (s.m.core.read .rsp).toNat - 40 := by
    rw [hur]; omega
  have q3 : ((u.m.core.read .rsp).toNat + 184) % 18446744073709551616 = (s.m.core.read .rsp).toNat - 32 := by
    rw [hur]; omega
  have q4 : ((u.m.core.read .rsp).toNat + 192) % 18446744073709551616 = (s.m.core.read .rsp).toNat - 24 := by
    rw [hur]; omega
  have q5 : ((u.m.core.read .rsp).toNat + 200) % 18446744073709551616 = (s.m.core.read .rsp).toNat - 16 := by
    rw [hur]; omega
  have q6 : ((u.m.core.read .rsp).toNat + 208) % 18446744073709551616 = (s.m.core.read .rsp).toNat - 8 := by
    rw [hur]; omega
  have q7 : ((u.m.core.read .rsp).toNat + 216) % 18446744073709551616 = (s.m.core.read .rsp).toNat := by
    rw [hur]; omega
  refine must_listed (o := 320) shaD_listing_ok.2.2 rfl hB.done (hin _ (by decide)) hDF (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, q1, sv1]
  refine must_listed (o := 321) shaD_listing_ok.2.2 rfl hB.done (hin _ (by decide)) hDF (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, q2, sv2]
  refine must_listed (o := 323) shaD_listing_ok.2.2 rfl hB.done (hin _ (by decide)) hDF (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, q3, sv3]
  refine must_listed (o := 325) shaD_listing_ok.2.2 rfl hB.done (hin _ (by decide)) hDF (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, q4, sv4]
  refine must_listed (o := 327) shaD_listing_ok.2.2 rfl hB.done (hin _ (by decide)) hDF (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, q5, sv5]
  refine must_listed (o := 329) shaD_listing_ok.2.2 rfl hB.done (hin _ (by decide)) hDF (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, q6, sv7]
  refine must_listed (o := 330) shaD_listing_ok.2.2 rfl hB.done (hin _ (by decide)) hDF (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, q7, hret]
  refine k _ ⟨rfl, ?_, ?_⟩ rfl (by simp) rfl (by simp [hB.fs])
  · simp only [st_read_mk, Silmaril.Machine.RegisterFile.write_same]; rw [hB.rsp]; bv_omega
  · intro r hr
    simp only [Silmaril.X86.sysv64_calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end Silmaril.Elf.Link.Dyn.Sha256sum
