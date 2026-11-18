module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MixedLoop
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.QuoteTail

/-! # GNU `sha256sum F1 … Fn`: a refused operand in the operand loop (`Task.errStep`)

`task_errStep`: from the call of `digest_file` (`0x2b81`) on an operand the file system refuses
to its return (`0x2b86`, `al = 0`): `call2b81`, `digest_file`'s error path on the extended process
(`task_digestOpenErrX_ok`: `quotef`, `error`), then the loop's frame again. The facts `main`'s
frame needs after the call come from `DigErrExit` (`keep`, the permissions of `*missing`
(`permMX`), `slot0`'s facts, `lib`/`npriv` for `program_invocation_name`).

The image facts survive the write of `slot0` (`ShaMem.keepQ`, `ShaMemP.keepQ`, `ShaMemM.keepQ`,
`ShaMemAll.keepQ`, `ShaMainAll.keepQ`: every fact lies outside `0xa060`–`0xa160`).
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
open Silmaril.Elf.Link.Dyn.ProcG
open Silmaril.Elf.Link.Dyn.Streams
open Silmaril.Elf.Link.Dyn.Imports
open Silmaril.Elf.Link.Dyn.Cert

theorem ShaMem.keepQ {b lb : Word} (hb : b.toNat + 0xa188 < 2 ^ 64) {m m' : Memory}
    (hm : ShaMem b lb m) (h : Keeps (ImgQ b) m m') : ShaMem b lb m' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hm
  obtain ⟨l1, l2, l3, l4⟩ := sha_lens
  have hl : ∀ {off : Nat}, off + 8 ≤ 0xa060 → loadN m' (b + BitVec.ofNat 64 off) 8 =
      loadN m (b + BitVec.ofNat 64 off) 8 := by
    intro off ho
    simp only [loadN, Memory.readBytes]
    rw [skeeps_range hb h (by omega) (fun k hk => ⟨⟨by omega, by omega⟩, by unfold Slot0; omega⟩)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Loaded Memory.fetchBytes at h1 ⊢
    rw [l1] at h1 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, by unfold Slot0; omega⟩)]; exact h1
  · unfold Loaded Memory.fetchBytes at h2 ⊢
    rw [l2] at h2 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, by unfold Slot0; omega⟩)]; exact h2
  · unfold Loaded Memory.fetchBytes at h3 ⊢
    rw [l3] at h3 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, by unfold Slot0; omega⟩)]; exact h3
  · unfold Loaded Memory.fetchBytes at h4 ⊢
    rw [l4] at h4 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, by unfold Slot0; omega⟩)]; exact h4
  · exact (hl (off := 0x9fb0) (by decide)).trans h5
  · exact (hl (off := 0x9fd8) (by decide)).trans h6
  · exact (hl (off := 0x9fe0) (by decide)).trans h7
  · exact (hl (off := 0x9fe8) (by decide)).trans h8
  · exact (hl (off := 0x9fa8) (by decide)).trans h9
  · exact (hl (off := 0xa008) (by decide)).trans h10

theorem ShaMemP.keepQ {b lb sc : Word} (hb : b.toNat + 0xa188 < 2 ^ 64) {m m' : Memory}
    (hm : ShaMemP b lb sc m) (h : Keeps (ImgQ b) m m') : ShaMemP b lb sc m' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hm
  have l1 := shaC_lens.1
  obtain ⟨l2, l3, l4, l5⟩ := shaP_lens
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
  · unfold Loaded Memory.fetchBytes at h5 ⊢
    rw [l5] at h5 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, by unfold Slot0; omega⟩)]; exact h5
  · unfold Memory.readBytes at h6 ⊢
    rw [skeeps_range (off := 0x7238) hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, by unfold Slot0; omega⟩)]; exact h6
  · unfold Memory.readBytes at h7 ⊢
    rw [skeeps_range (off := 0x71e0) hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, by unfold Slot0; omega⟩)]; exact h7
  · exact (hl (off := 0x9dd8) (by decide)).trans h8
  · exact (hl (off := 0x9ef8) (by decide)).trans h9
  · exact (hl (off := 0x9f70) (by decide)).trans h10
  · exact (hl (off := 0x9f98) (by decide)).trans h11
  · exact (hl (off := 0x9df0) (by decide)).trans h12

theorem ShaMemM.keepQ {b lb sr : Word} (hb : b.toNat + 0xa188 < 2 ^ 64) {m m' : Memory}
    (hm : ShaMemM b lb sr m) (h : Keeps (ImgQ b) m m') : ShaMemM b lb sr m' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, r1, r2, r3⟩ := hm
  obtain ⟨l1, l2, l3, l4, l5⟩ := shaM_lens
  have hl : ∀ {off : Nat}, off + 8 ≤ 0xa060 → loadN m' (b + BitVec.ofNat 64 off) 8 =
      loadN m (b + BitVec.ofNat 64 off) 8 := by
    intro off ho
    simp only [loadN, Memory.readBytes]
    rw [skeeps_range hb h (by omega) (fun k hk => ⟨⟨by omega, by omega⟩, by unfold Slot0; omega⟩)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Loaded Memory.fetchBytes at h1 ⊢
    rw [l1] at h1 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, by unfold Slot0; omega⟩)]; exact h1
  · unfold Loaded Memory.fetchBytes at h2 ⊢
    rw [l2] at h2 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, by unfold Slot0; omega⟩)]; exact h2
  · unfold Loaded Memory.fetchBytes at h3 ⊢
    rw [l3] at h3 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, by unfold Slot0; omega⟩)]; exact h3
  · unfold Loaded Memory.fetchBytes at h4 ⊢
    rw [l4] at h4 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, by unfold Slot0; omega⟩)]; exact h4
  · unfold Loaded Memory.fetchBytes at h5 ⊢
    rw [l5] at h5 ⊢; rw [skeeps_range hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, by unfold Slot0; omega⟩)]; exact h5
  · unfold Memory.readBytes at h6 ⊢
    rw [skeeps_range (off := 0x716e) hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, by unfold Slot0; omega⟩)]; exact h6
  · unfold Memory.readBytes at h7 ⊢
    rw [skeeps_range (off := 0xa01c) hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, by unfold Slot0; omega⟩)]; exact h7
  · unfold Memory.readBytes at h8 ⊢
    rw [skeeps_range (off := 0xa170) hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, by unfold Slot0; omega⟩)]
    exact h8
  · exact (hl (off := 0x9de0) (by decide)).trans h9
  · exact (hl (off := 0x9e70) (by decide)).trans h10
  · exact (hl (off := 0x9e78) (by decide)).trans h11
  · exact (hl (off := 0x9e90) (by decide)).trans h12
  · exact (hl (off := 0x9eb0) (by decide)).trans h13
  · exact (hl (off := 0x9f18) (by decide)).trans h14
  · exact (hl (off := 0x9f38) (by decide)).trans h15
  · exact (hl (off := 0x9fa0) (by decide)).trans h16
  · exact (hl (off := 0x9fb8) (by decide)).trans h17
  · exact (hl (off := 0x9fc8) (by decide)).trans h18
  · exact r1.keep h fun k hk => by
      rw [addr_toNat (by omega)]; rw [l1] at hk; exact ⟨⟨by omega, by omega⟩, by unfold Slot0; omega⟩
  · exact r2.keep h fun k hk => by
      rw [addr_toNat (by omega)]; rw [l2] at hk; exact ⟨⟨by omega, by omega⟩, by unfold Slot0; omega⟩
  · exact r3.keep h fun k hk => by
      rw [addr_toNat (by omega)]; rw [l3] at hk; exact ⟨⟨by omega, by omega⟩, by unfold Slot0; omega⟩

theorem loaded_keepQ {b : Word} (hb : b.toNat + 0xa188 < 2 ^ 64) {m m' : Memory} (h : Keeps (ImgQ b) m m')
    {off : Nat} {code : List Byte} (hr : off + code.length ≤ 0xa060)
    (hl : Loaded m (b + BitVec.ofNat 64 off) code) : Loaded m' (b + BitVec.ofNat 64 off) code := by
  unfold Loaded Memory.fetchBytes at hl ⊢
  rw [skeeps_range hb h (by omega) (fun k hk => ⟨⟨by omega, by omega⟩, by unfold Slot0; omega⟩)]
  exact hl

theorem codeRO_keepQ {b : Word} (hb : b.toNat + 0xa188 < 2 ^ 64) {m m' : Memory} (h : Keeps (ImgQ b) m m')
    {off : Nat} {code : List Byte} (hr : off + code.length ≤ 0xa060)
    (hc : CodeRO m (b + BitVec.ofNat 64 off) code) : CodeRO m' (b + BitVec.ofNat 64 off) code := by
  intro k hk
  have e : (b + BitVec.ofNat 64 off).toNat = b.toNat + off := addr_toNat (by omega)
  have := hc k hk
  rw [e] at this ⊢
  rw [(h _ ⟨⟨by omega, by omega⟩, by unfold Slot0; omega⟩).2]
  exact this

theorem ShaMainAll.keepQ {b : Word} (hb : b.toNat + 0xa188 < 2 ^ 64) {m m' : Memory}
    (hm : ShaMainAll b m) (h : Keeps (ImgQ b) m m') : ShaMainAll b m' := by
  obtain ⟨l0, l1, l2, l3, l4, l5, l6, l7, l8, l9⟩ := mainAll_lens
  exact ⟨loaded_keepQ hb h (by omega) hm.ld0, codeRO_keepQ hb h (by omega) hm.ro0,
    loaded_keepQ hb h (by omega) hm.ld1, codeRO_keepQ hb h (by omega) hm.ro1,
    loaded_keepQ hb h (by omega) hm.ld2, codeRO_keepQ hb h (by omega) hm.ro2,
    loaded_keepQ hb h (by omega) hm.ld3, codeRO_keepQ hb h (by omega) hm.ro3,
    loaded_keepQ hb h (by omega) hm.ld4, codeRO_keepQ hb h (by omega) hm.ro4,
    loaded_keepQ hb h (by omega) hm.ld5, codeRO_keepQ hb h (by omega) hm.ro5,
    loaded_keepQ hb h (by omega) hm.ld6, codeRO_keepQ hb h (by omega) hm.ro6,
    loaded_keepQ hb h (by omega) hm.ld7, codeRO_keepQ hb h (by omega) hm.ro7,
    loaded_keepQ hb h (by omega) hm.ld8, codeRO_keepQ hb h (by omega) hm.ro8,
    loaded_keepQ hb h (by omega) hm.ld9, codeRO_keepQ hb h (by omega) hm.ro9⟩

theorem ShaMemAll.keepQ {b lb kb sr sc : Word} (hb : b.toNat + 0xa188 < 2 ^ 64) {m m' : Memory}
    (hm : ShaMemAll b lb kb sr sc m) (h : Keeps (ImgQ b) m m') : ShaMemAll b lb kb sr sc m' :=
  ⟨hm.st.keepQ hb h, hm.cl.keepQ hb h, hm.dg.keepQ hb h, hm.pr.keepQ hb h, hm.mn.keepQ hb h⟩

theorem low8_of_low32_0 {x : Word} (h : low32 x = 0#32) : x.setWidth 8 = 0#8 := by
  have := congrArg (BitVec.setWidth 8) h
  rw [low32, BitVec.setWidth_setWidth_of_le _ (by decide)] at this
  exact this

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`Task.errStep` holds** for `ErrMem`, given `error`'s and `__errno_location`'s contracts, a
16-byte aligned base, `errno` below the streams, and the argument area, the guard, the library's
stream variables and `program_invocation_name` outside the image. -/
theorem task_errStep {E : Env} {R : ShaRep} {W : World} {b lb kb sr sc pinA : Word} {s : PState}
    {prog : List Byte} (K : ErrImps E W lb pinA) (hal16 : b.toNat % 16 = 0)
    (herrLo : E.errnoA.toNat + 4 ≤ E.S.lo) (hargsI : ∀ a, W.args a → ¬ ShaImg b a)
    (hguardI : ∀ j, j < 8 → ¬ ShaImg b ((s.m.core.fsBase + 0x28#64).toNat + j))
    (hvarI : ∀ a, ShaImg b a → ¬ VarR lb a) (hpinI : ∀ j, j < 8 → ¬ ShaImg b (pinA.toNat + j)) :
    Task.errStep E R W b lb kb sr sc s (ErrMem E W b lb pinA prog (s.m.core.read .rsp)) prog := by
  intro M c Q y q p n rest X g okv e hy hE hop k
  refine mustG_of_mustQ XG (s := y.view XG) (x := y.x) rfl ?_
  generalize y.view XG = v at hy hE k
  have F := hy.fr
  have I := M.dig.cl.img
  have hb := M.dig.cl.hb
  have hroom : Room W v.m.memory (s.m.core.read .rsp) 4096 := F.body.room
  have hsp := hroom.1
  have hsp2 := hroom.2.1
  have hlo := c.lo
  have hal := c.al
  have hKroom : ∀ a, (s.m.core.read .rsp).toNat - 4096 ≤ a → a < (s.m.core.read .rsp).toNat + 8 → ¬ W.Kept a :=
    fun a h1 h2 => (hroom.2.2 a h1 h2).2.2
  have hKout : ∀ a, W.Kept a → a < (s.m.core.read .rsp).toNat - 4096 ∨ (s.m.core.read .rsp).toNat + 8 ≤ a :=
    fun a ha => by by_contra hc; exact hKroom a (by omega) (by omega) ha
  have hImgK : ∀ a, ShaImg b a → W.Kept a := fun a ha => Or.inl (by rw [I]; exact ha)
  have hS0I : ∀ a, Slot0 b a → ShaImg b a := fun a ha => by unfold Slot0 at ha; unfold ShaImg; omega
  have hS0a : ∀ a, Slot0 b a → a < (s.m.core.read .rsp).toNat - 4096 ∨ (s.m.core.read .rsp).toNat + 8 ≤ a :=
    fun a ha => hKout a (hImgK a (hS0I a ha))
  have hvsp : v.m.core.read .rsp = s.m.core.read .rsp - 328#64 := F.body.rsp
  have e328 : (v.m.core.read .rsp).toNat = (s.m.core.read .rsp).toNat - 328 := by
    rw [hvsp]; exact sub_toNat (k := 328) (by omega) (by decide)
  have e336 : (v.m.core.read .rsp - 8#64).toNat = (s.m.core.read .rsp).toNat - 336 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), e328]; omega
  have eA0 : (s.m.core.read .rsp - 8#64 + 0xffffffffffffffa0#64).toNat = (s.m.core.read .rsp).toNat - 0x68 :=
    (fp_neg _ 0x60 (by omega) (by decide) (by decide)).trans (by omega)
  have e58 : (s.m.core.read .rsp - 8#64 + 0xffffffffffffff58#64).toNat = (s.m.core.read .rsp).toNat - 0xb0 :=
    (fp_neg _ 0xa8 (by omega) (by decide) (by decide)).trans (by omega)
  -- the call
  refine call2b81 I hb F.body.done F.ma F.rip
    (by rw [e336]; exact room_perm hroom (Or.inr rfl) (by omega) (by omega)) ?_
  have csp : ((callEntry v (b + 0x6a40#64) (b + 0x2b86#64)).m.core.read .rsp).toNat = (s.m.core.read .rsp).toNat - 336 := by
    rw [callEntry_rsp]; exact e336
  have hpushK : Keeps (fun a => a < (s.m.core.read .rsp).toNat - 336 ∨ (s.m.core.read .rsp).toNat - 328 ≤ a) v.m.memory
      (callEntry v (b + 0x6a40#64) (b + 0x2b86#64)).m.memory := by
    rw [callEntry_mem]; exact pushMem_keeps fun x hx => by rw [e336]; omega
  have hpushKK : Keeps W.Kept v.m.memory (callEntry v (b + 0x6a40#64) (b + 0x2b86#64)).m.memory :=
    hpushK.mono fun a ha => by rcases hKout a ha with h | h <;> omega
  have hcperm : ∀ acc a, (callEntry v (b + 0x6a40#64) (b + 0x2b86#64)).m.memory.permits acc a =
      v.m.memory.permits acc a := fun _ _ => by rw [callEntry_mem]; rfl
  have hroomC : Room W (callEntry v (b + 0x6a40#64) (b + 0x2b86#64)).m.memory (s.m.core.read .rsp) 4096 :=
    hroom.keeps fun a _ _ acc => hcperm acc a
  have hpr : v.m.memory.Permitted .read (v.m.core.read .rsp - 8#64).toNat 8 := by
    rw [e336]; exact room_perm hroom (Or.inl rfl) (by omega) (by omega)
  have hpw : v.m.memory.Permitted .write (v.m.core.read .rsp - 8#64).toNat 8 := by
    rw [e336]; exact room_perm hroom (Or.inr rfl) (by omega) (by omega)
  have hretC : (callEntry v (b + 0x6a40#64) (b + 0x2b86#64)).m.memory.readBytes
      ((callEntry v (b + 0x6a40#64) (b + 0x2b86#64)).m.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [b + 0x2b86#64]) := by
    rw [callEntry_rsp, callEntry_mem]; exact pushMem_read hpr hpw
  have hMc : ShaMemAll b lb kb sr sc (callEntry v (b + 0x6a40#64) (b + 0x2b86#64)).m.memory :=
    F.body.mem.keepW hb (hpushKK.mono fun a ha => Or.inl (by rw [I]; exact ha.1))
  have cfs : (callEntry v (b + 0x6a40#64) (b + 0x2b86#64)).m.core.fsBase = v.m.core.fsBase := rfl
  have crdi : (callEntry v (b + 0x6a40#64) (b + 0x2b86#64)).m.core.read .rdi = p := by
    rw [callEntry_read _ _ _ (by decide)]; exact hy.rdi
  have crsi : ((callEntry v (b + 0x6a40#64) (b + 0x2b86#64)).m.core.read .rsi).toNat = (s.m.core.read .rsp).toNat - 0x68 := by
    rw [callEntry_read _ _ _ (by decide), hy.rsi]; exact eA0
  have crdx : ((callEntry v (b + 0x6a40#64) (b + 0x2b86#64)).m.core.read .rdx).toNat = (s.m.core.read .rsp).toNat - 0xb0 := by
    rw [callEntry_read _ _ _ (by decide), hy.rdx]; exact e58
  obtain ⟨hn1, hn2, hn3, hn4, hn5⟩ := F.args
  have hnameC : CStr (callEntry v (b + 0x6a40#64) (b + 0x2b86#64)).m.memory p n :=
    cstr_keeps hpushKK hn3 fun j hj => Or.inr (Or.inl (hn4 j hj))
  -- `ErrMem` at the call
  have hEc : ErrMem E W b lb pinA prog (s.m.core.read .rsp) (callEntry v (b + 0x6a40#64) (b + 0x2b86#64)).m.memory :=
    hE.keepS (hpushK.mono fun a ha => by omega)
      (E.S.priv_keep _ _ (hpushK.mono fun a ha => by have := E.S.priv_lo _ _ ha; omega))
  have hpinNPo : ∀ j, j < 8 → NPo E b (callEntry v (b + 0x6a40#64) (b + 0x2b86#64)) (pinA.toNat + j) := by
    intro j hj
    obtain ⟨h1, h2⟩ := hEc.pinNP j hj
    have hS := hE.pinS j hj
    refine ⟨h1, h2, fun hs => hpinI j hj (hS0I _ hs), fun hd => ?_, ?_⟩
    · simp only [DX, crsi, crdx] at hd; omega
    · rw [csp]; rcases hE.pinLo j hj with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
  have hEntry : DigEntryE E W b lb kb pinA (callEntry v (b + 0x6a40#64) (b + 0x2b86#64)) n e g prog := by
    refine ⟨rfl, Silmaril.Elf.Link.Dyn.Hello.abiEntry_of (by rw [csp]; omega) hretC,
      ⟨by rw [csp]; omega, by rw [csp]; omega, fun a h1 h2 => by
        rw [csp] at h1 h2; rw [hcperm, hcperm]; exact hroom.2.2 a (by omega) (by omega)⟩,
      by rw [csp]; omega, F.body.done, ⟨hMc.cl, hMc.dg⟩, hEc.memK, hEc.ro, hEc.qimps, hEc.slots, hEc.slot0,
      by rw [crdi]; exact hnameC,
      fun j hj => by rw [crdi]; exact ⟨Or.inr (Or.inl (hn4 j hj)), fun hs => hargsI _ (hn4 j hj) (hS0I _ hs)⟩,
      by rw [crdi]; exact notDash_of_cstr hnameC hop.nd, hop.file, hop.fits,
      fun a ha => ?_, ?_, ?_, ?_, ?_, ?_, by rw [cfs, F.fs]; exact c.guardk,
      fun j hj hs => by rw [cfs, F.fs] at hs; exact hguardI j hj (hS0I _ hs), herrLo, hEc.progN, hpinNPo,
      hEc.progk⟩
    · simp only [DX, crsi, crdx] at ha
      refine ⟨hKroom a (by omega) (by omega), by rw [csp]; omega⟩
    · rw [crsi]; exact room_perm hroomC (Or.inr rfl) (by omega) (by omega)
    · rw [crsi]; exact room_perm hroomC (Or.inl rfl) (by omega) (by omega)
    · rw [crdx]; exact room_perm hroomC (Or.inr rfl) (by omega) (by omega)
    · rw [crdx]; exact room_perm hroomC (Or.inl rfl) (by omega) (by omega)
    · rw [cfs, F.fs, loadN_keeps hpushKK (fun j hj => c.guardk j hj)]; exact F.guard
  refine must_done fun x' hx' => ?_
  refine task_digestOpenErrX_ok hal16 M.dig K Q ⟨x', (callEntry v (b + 0x6a40#64) (b + 0x2b86#64)).g⟩ n e g prog
    hop.plain (by rw [xview_mk hx']; exact hEntry) fun z hz => ?_
  rw [xview_mk hx'] at hz
  -- after the call
  have hMXa : ∀ a, MX (callEntry v (b + 0x6a40#64) (b + 0x2b86#64)) a → a = (s.m.core.read .rsp).toNat - 0xb0 :=
    fun a h => by unfold MX at h; rw [crdx] at h; omega
  have hMXnk : ∀ a, MX (callEntry v (b + 0x6a40#64) (b + 0x2b86#64)) a → ¬ W.Kept a :=
    fun a h => hKroom a (by have := hMXa a h; omega) (by have := hMXa a h; omega)
  have hKvw : Keeps (fun a => (W.Kept a ∨ (s.m.core.read .rsp).toNat - 328 ≤ a) ∧
      ¬ MX (callEntry v (b + 0x6a40#64) (b + 0x2b86#64)) a ∧ ¬ Slot0 b a) v.m.memory (z.view XG).m.memory := by
    refine (hpushK.mono fun a ha => ?_).trans (hz.keep.mono fun a ha => ⟨?_, ?_⟩)
    · rcases ha.1 with h | h
      · rcases hKout a h with h' | h' <;> omega
      · omega
    · rcases ha.1 with h | h
      · exact Or.inl h
      · right; rw [csp]; omega
    · rintro (h | h)
      · exact ha.2.1 h
      · exact ha.2.2 h
  have hfr : ∀ a, (s.m.core.read .rsp).toNat - 328 ≤ a → a < (s.m.core.read .rsp).toNat + 8 →
      a ≠ (s.m.core.read .rsp).toNat - 0xb0 → (W.Kept a ∨ (s.m.core.read .rsp).toNat - 328 ≤ a) ∧
      ¬ MX (callEntry v (b + 0x6a40#64) (b + 0x2b86#64)) a ∧ ¬ Slot0 b a :=
    fun a h1 h2 h3 => ⟨Or.inr h1, fun hm => h3 (hMXa a hm), fun hs => by have := hS0a a hs; omega⟩
  have hkk : ∀ a, W.Kept a → ¬ Slot0 b a → (W.Kept a ∨ (s.m.core.read .rsp).toNat - 328 ≤ a) ∧
      ¬ MX (callEntry v (b + 0x6a40#64) (b + 0x2b86#64)) a ∧ ¬ Slot0 b a :=
    fun a h1 h2 => ⟨Or.inl h1, fun hm => hMXnk a hm h1, h2⟩
  have hQv : Keeps (ImgQ b) v.m.memory (z.view XG).m.memory :=
    hKvw.mono fun a ha => hkk a (hImgK a ha.1) ha.2
  have hIQ : ∀ m j : Nat, m + j < 0xa188 → (m + j < 0xa060 ∨ 0xa160 ≤ m + j) →
      ImgQ b ((b + BitVec.ofNat 64 m).toNat + j) := fun m j h1 h2 => by
    rw [addr_toNat (by omega)]; exact ⟨⟨by omega, by omega⟩, by unfold Slot0; omega⟩
  have hMw : ShaMemAll b lb kb sr sc (z.view XG).m.memory := F.body.mem.keepQ hb hQv
  have hsv6 : ∀ p ∈ sv6 (reb s v.m.memory), 8 ≤ p.1 ∧ p.1 ≤ 48 := by
    intro q hq
    simp only [sv6, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  have hdw : (z.view XG).g.done = none := by rw [hz.gdone]; exact F.body.done
  obtain ⟨hBw, hripw, -, hcsw⟩ := body_now
    (F := fun a => MX (callEntry v (b + 0x6a40#64) (b + 0x2b86#64)) a ∨ Slot0 b a)
    F.body (by omega) hsv6 (by omega) (by omega) hz.abi hz.keep hz.perm
    (fun a hF h1 h2 acc => by
      rcases hF with hm | hs
      · rw [hz.permMX a hm acc, hcperm]
      · exact absurd (hImgK a (hS0I a hs)) (hKroom a h1 h2))
    (fun a hF => by
      rcases hF with hm | hs
      · left; have := hMXa a hm; show a + 48 < (s.m.core.read .rsp).toNat; omega
      · rcases hS0a a hs with h | h
        · left; show a + 48 < (s.m.core.read .rsp).toNat; omega
        · right; exact h)
    hMw hz.fs hdw
  have hcs : ∀ r ∈ [Reg.rbx, .rbp, .r12, .r14, .r15], r ∈ Silmaril.X86.sysv64.calleeSaved := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [Silmaril.X86.sysv64_calleeSaved]
  have e18 : (s.m.core.read .rsp - 8#64 + 0xffffffffffffff18#64).toNat = (s.m.core.read .rsp).toNat - 240 :=
    (fp_neg _ 0xe8 (by omega) (by decide) (by decide)).trans (by omega)
  have e28 : (s.m.core.read .rsp - 8#64 + 0xffffffffffffff28#64).toNat = (s.m.core.read .rsp).toNat - 224 :=
    (fp_neg _ 0xd8 (by omega) (by decide) (by decide)).trans (by omega)
  have e20 : (s.m.core.read .rsp - 8#64 + 0xffffffffffffff20#64).toNat = (s.m.core.read .rsp).toNat - 232 :=
    (fp_neg _ 0xe0 (by omega) (by decide) (by decide)).trans (by omega)
  obtain ⟨sto, hso, hse, hsr, hsX⟩ := F.out
  obtain ⟨st', hs', -, -, hrd', hcase⟩ := hz.out sto ⟨by rw [callEntry_mem]; exact file_push hso.1 (by rw [e336]; omega), hso.2⟩
  have hX' : (z.view XG).g.out ++ st'.buf = X ∧ st'.err = false := by
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, -⟩
    · refine ⟨?_, by rw [h2, hse]⟩
      rw [h1, callEntry_g, List.append_nil, hsX]
    · rw [M.rel] at h1; cases h1
  -- `program_invocation_name` after the call
  have hpinw : loadN (z.view XG).m.memory pinA 8 =
      loadN (callEntry v (b + 0x6a40#64) (b + 0x2b86#64)).m.memory pinA 8 :=
    loadN_keeps hz.lib fun j hj => hpinNPo j hj
  have hQc : Keeps (ImgQ b) (callEntry v (b + 0x6a40#64) (b + 0x2b86#64)).m.memory (z.view XG).m.memory :=
    hz.keep.mono fun a ha => ⟨Or.inl (hImgK a ha.1), by
      rintro (hm | hs)
      · exact hMXnk a hm (hImgK a ha.1)
      · exact ha.2 hs⟩
  have hEw : ErrMem E W b lb pinA prog (s.m.core.read .rsp) (z.view XG).m.memory := by
    refine ⟨hEc.memK.keepQ hb hQc, hEc.ro.keep (hQc.mono fun a ha => ⟨⟨by omega, by omega⟩, by unfold Slot0; omega⟩),
      hEc.qimps.keep hQc, hz.slots, hz.slot0, ?_, fun j hj => ⟨hz.npriv _ (hpinNPo j hj), ?_⟩,
      fun pa hpa => hEc.progk pa (by rw [← hpinw]; exact hpa), hE.pinS, hE.pinLo, hE.keptS, hE.lo⟩
    · obtain ⟨pa, hpa, hc⟩ := hEc.progN
      refine ⟨pa, by rw [hpinw]; exact hpa, cstr_keeps hz.keep hc fun j hj => ?_⟩
      obtain ⟨h1, h2⟩ := hEc.progk pa hpa j hj
      exact ⟨Or.inl h1, by rintro (hm | hs); exact hMXnk _ hm h1; exact h2 hs⟩
    · rw [(hz.lib _ (hpinNPo j hj)).2]; exact (hpinNPo j hj).2.1
  refine k z ⟨hBw, F.ma.keepQ hb hQv,
    by rw [loadN_keeps hQv (fun j hj => hIQ 0xa040 j (by omega) (by omega))]; exact F.bss,
    (hQv.permitted (fun j hj => hIQ 0xa040 j (by omega) (by omega))).2 F.bssw,
    by rw [loadN_keeps hQv (fun j hj => hIQ 0xa160 j (by omega) (by omega))]; exact F.hr,
    hripw, by rw [hcsw .rbp (hcs .rbp (by simp))]; exact F.rbp, by rw [hcsw .rbx (hcs .rbx (by simp))]; exact F.rbx,
    by rw [hcsw .r12 (hcs .r12 (by simp))]; exact F.r12, by rw [hcsw .r14 (hcs .r14 (by simp))]; exact F.r14,
    by rw [hcsw .r15 (hcs .r15 (by simp))]; exact F.r15, hz.fs.trans F.fs, by rw [hz.gjobs]; exact F.jobs,
    by rw [hz.gatexit]; exact F.atexit,
    by rw [loadN_keeps hKvw (fun j hj => hkk _ (c.guardk j hj) (fun hs => hguardI j hj (hS0I _ hs)))]; exact F.guard,
    ?_, ⟨st', hs', hX'.2, by rw [hrd', hsr], hX'.1⟩,
    hz.streams _ _ (Ne.symm M.ne) (by rw [callEntry_mem]; exact file_push F.err (by rw [e336]; omega)),
    F.vars.keepR (hKvw.mono fun a ha => ?_), ?_, ?_,
    by rw [loadN_keeps hQv (fun j hj => hIQ 0xa178 j (by omega) (by omega))]; exact F.len,
    ?_, F.qlim, ?_, ?_, ?_, ArgsAt.keep (hKvw.mono fun a h => hkk a (Or.inr (Or.inl h))
      (fun hs => hargsI a h (hS0I a hs))) ⟨hn1, hn2, hn3, hn4, hn5⟩,
    ?_⟩ (by rw [hz.gerr]; rfl) hEw
    (low8_of_low32_0 hz.ret)
  · rw [hKvw.readBytes (fun j hj => hfr _ (by omega) (by omega) (by omega))]
    exact F.guards
  · have hK : W.Kept a := by
      have := F.vars.kept (a - (lb + 0x2056a0#64).toNat) (by simp only [VarR] at ha; omega)
      rwa [show (lb + 0x2056a0#64).toNat + (a - (lb + 0x2056a0#64).toNat) = a by
        simp only [VarR] at ha; omega] at this
    exact hkk a hK fun hs => hvarI a (hS0I a hs) ha
  · rw [hKvw.readBytes (fun j hj => hfr _ (by omega) (by omega) (by omega))]
    exact F.tag
  · rw [hKvw.readBytes (fun j hj => hfr _ (by omega) (by omega) (by omega))]
    exact F.bin
  · rw [loadN_keeps hKvw (fun j hj => by rw [e18]; exact hfr _ (by omega) (by omega) (by omega))]
    exact F.endp
  · rw [loadN_keeps hKvw (fun j hj => by rw [e28]; exact hfr _ (by omega) (by omega) (by omega))]
    exact F.ok
  · rw [loadN_keeps hKvw (fun j hj => by rw [e20]; exact hfr _ (by omega) (by omega) (by omega))]
    exact F.dsl
  · rw [hKvw.readBytes (fun j hj => hfr _ (by omega) (by omega) (by omega))]
    exact F.ret
  · obtain ⟨⟨js, hjs⟩, h1, h2, h3⟩ := hy.res
    refine ⟨⟨js, by rw [hz.gjobs]; exact hjs⟩, ?_, ?_, ?_⟩
    · rw [hz.gallocs]; simp only [callEntry_g]; omega
    · rw [hz.gheap]; simp only [callEntry_g]; omega
    · rw [hz.gfiles]; simp only [callEntry_g]; omega

end Silmaril.Elf.Link.Dyn.Sha256sum
