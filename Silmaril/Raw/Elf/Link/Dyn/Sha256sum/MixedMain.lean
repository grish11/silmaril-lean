module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MixedLoop
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MultiMain

/-! # GNU `sha256sum F1 … Fn` with refused operands: `main`'s entry to the end of the process

* `mixed_head` (PROVED): `main` from its entry to the first operand's `digest_file`
  (`sha_main_headP`, `sha_main_bufP`, `sha_main_getoptP`, `multi_preK`), establishing the loop's
  invariant with `ErrMem`: `program_invocation_name = argv[0]` (stored by `set_program_name`,
  kept by the library calls since it is non-private memory outside their footprints), and the
  image facts of the refused path (`MixedEntry` at `main`'s entry, kept since the head writes
  no image byte below the option variables);
* `sha_main_mixed`: from `main`'s entry, on the extended process, every run halts with status 0
  iff no operand was refused, `stdout` = the readable operands' lines and `stderr` the
  diagnostics `prog: NAME: strerror(e)\n`, in order — conditional on `Task.okExt` and
  `Task.errStep` (`MixedLoop`).
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

/-- **What the refused path needs of `main`'s entry beyond `MainEntryF`** (image facts from the
loader, and where `program_invocation_name` and `argv[0]` lie). -/
structure MixedEntry (E : Env) (W : World) (b lb : Word) (s : PState) (a0p : Word) (a0 : List Byte) : Prop where
  memK : ShaMemK b lb s.m.memory
  ro : ShaRO b lb s.m.memory
  qimps : QImps E W b lb s.m.memory
  slots : QSlots b s.m.memory
  slot0 : ∀ a, Slot0 b a → s.m.memory.permits .read a = true ∧ s.m.memory.permits .write a = true
  pinOpt : ∀ a, PinR lb a → ¬ OptR E a
  pinLo : ∀ j, j < 8 → (lb + 0x205378#64).toNat + j < E.S.lo ∨
    (s.m.core.read .rsp).toNat + 8 ≤ (lb + 0x205378#64).toNat + j
  a0img : ∀ j, j < a0.length + 1 → ¬ ShaImg b (a0p.toNat + j)

theorem ShaMemK.keepW {b lb : Word} (hb : b.toNat + 0xa188 < 2 ^ 64) {m m' : Memory}
    (hm : ShaMemK b lb m) (h : Keeps (ImgW b) m m') : ShaMemK b lb m' := by
  obtain ⟨h1, h2, h3, h4⟩ := hm
  have hl : ∀ {off : Nat}, off + 8 ≤ 0xa160 → loadN m' (b + BitVec.ofNat 64 off) 8 =
      loadN m (b + BitVec.ofNat 64 off) 8 := by
    intro off ho
    simp only [loadN, Memory.readBytes]
    rw [skeeps_range hb h (by omega) (fun k hk => ⟨⟨by omega, by omega⟩, Or.inl (by omega)⟩)]
  refine ⟨(hl (off := 0x9de8) (by decide)).trans h1, (hl (off := 0x9f40) (by decide)).trans h2, ?_, ?_⟩
  · unfold Memory.readBytes at h3 ⊢
    rw [skeeps_range (off := 0x70fa) hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, Or.inl (by omega)⟩)]
    exact h3
  · unfold Memory.readBytes at h4 ⊢
    rw [skeeps_range (off := 0xa171) hb h (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, Or.inr ⟨by omega, by omega⟩⟩)]
    exact h4

theorem QSlots.keepW {b : Word} (hb : b.toNat + 0xa188 < 2 ^ 64) {m m' : Memory} (h : QSlots b m)
    (hk : Keeps (ImgW b) m m') : QSlots b m' := by
  have hl : ∀ {off n : Nat}, off + n ≤ 0xa060 → loadN m' (b + BitVec.ofNat 64 off) n =
      loadN m (b + BitVec.ofNat 64 off) n := by
    intro off n ho
    simp only [loadN, Memory.readBytes]
    rw [skeeps_range hb hk (by omega) (fun k hk => ⟨⟨by omega, by omega⟩, Or.inl (by omega)⟩)]
  exact ⟨(hl (off := 0xa010) (by decide)).trans h.nslots, (hl (off := 0xa020) (by decide)).trans h.size,
    (hl (off := 0xa028) (by decide)).trans h.val, (hl (off := 0xa030) (by decide)).trans h.vec⟩

theorem QImps.keepW {E : Env} {W : World} {b lb : Word} {m m' : Memory} (h : QImps E W b lb m)
    (hk : Keeps (ImgW b) m m') : QImps E W b lb m' := by
  obtain ⟨a, ha, hi⟩ := h.memcmp
  refine ⟨h.lz, h.img, h.hb, h.errno, h.mbcur, a, ?_, hi⟩
  rw [← ha]; simp only [loadN, Memory.readBytes]
  rw [skeeps_range (off := 0x9e18) h.hb hk (by decide) (fun k hk => ⟨⟨by omega, by omega⟩, Or.inl (by omega)⟩)]

/-- `ErrMem` at the loop's head, from the facts the head keeps. -/
theorem errMem_head {E : Env} {R : ShaRep} {W : World} {b lb kb sc : Word} (M : MultiImps E R W b lb kb sc)
    {C : Nat → Prop} {s z v : PState} {a0p : Word} {a0 : List Byte}
    (hX : MixedEntry E W b lb s a0p a0) (hlo : E.S.lo + 4096 ≤ (s.m.core.read .rsp).toNat)
    (hC : ∀ a, C a → a < (s.m.core.read .rsp).toNat - 4096 ∨ (s.m.core.read .rsp).toNat + 8 ≤ a)
    (hpinC : ∀ a, PinR lb a → C a) (hpinK : ∀ a, PinR lb a → ¬ W.Kept a)
    (ha0s : CStr s.m.memory a0p a0) (ha0k : ∀ j, j < a0.length + 1 → W.Kept (a0p.toNat + j))
    (hroom : Room W v.m.memory (s.m.core.read .rsp) 4096)
    (hpz : ∀ a, PinR lb a → ¬ E.S.priv z.m.memory a ∧ z.m.memory.permits .read a = true)
    (hpinv : loadN v.m.memory (lb + 0x205378#64) 8 = some a0p)
    (hkzv : Keeps (fun a => ¬ ShaImg b a ∧ (a < (s.m.core.read .rsp).toNat - 4096 ∨ (s.m.core.read .rsp).toNat + 8 ≤ a))
      z.m.memory v.m.memory)
    (hKSV : Keeps (fun a => ImgW b a ∨ (W.Kept a ∧ ¬ ShaImg b a)) s.m.memory v.m.memory) :
    ErrMem E W b lb (lb + 0x205378#64) a0 (s.m.core.read .rsp) v.m.memory := by
  have hb := hX.qimps.hb
  have hImgK : ∀ a, ShaImg b a → W.Kept a := fun a ha => Or.inl (by rw [hX.qimps.img]; exact ha)
  have hKout : ∀ a, W.Kept a → a < (s.m.core.read .rsp).toNat - 4096 ∨ (s.m.core.read .rsp).toNat + 8 ≤ a :=
    fun a ha => by by_contra hc; exact (hroom.2.2 a (by omega) (by omega)).2.2 ha
  have hKI : Keeps (ImgW b) s.m.memory v.m.memory := hKSV.mono fun a ha => Or.inl ha
  have hpin : ∀ j, j < 8 → PinR lb ((lb + 0x205378#64).toNat + j) := fun j hj => ⟨by omega, by omega⟩
  have hprv : E.S.priv v.m.memory = E.S.priv z.m.memory :=
    E.S.priv_keep _ _ (hkzv.mono fun a ha => ⟨fun hI => M.apart _ _ (hImgK a hI) ha,
      Or.inl (by have := E.S.priv_lo _ _ ha; omega)⟩)
  refine ⟨hX.memK.keepW hb hKI, hX.ro.keep (hKI.mono fun a ha => ⟨⟨by omega, by omega⟩, Or.inl (by omega)⟩),
    hX.qimps.keepW hKI, hX.slots.keepW hb hKI, fun a ha => ?_,
    ⟨a0p, hpinv, cstr_keeps hKSV ha0s fun j hj => Or.inr ⟨ha0k j hj, hX.a0img j hj⟩⟩, fun j hj => ?_,
    fun pa hpa j hj => ?_, fun j hj => hC _ (hpinC _ (hpin j hj)), hX.pinLo, hKout, hlo⟩
  · have hw : ImgW b a := by unfold Slot0 at ha; exact ⟨⟨by omega, by omega⟩, Or.inl (by omega)⟩
    obtain ⟨h1, h2⟩ := hX.slot0 a ha
    exact ⟨by rw [(hKI a hw).2]; exact h1, by rw [(hKI a hw).2]; exact h2,
      fun hp => M.apart _ _ (hImgK a hw.1) hp⟩
  · have hk := hkzv _ ⟨fun hI => hpinK _ (hpin j hj) (hImgK _ hI), hC _ (hpinC _ (hpin j hj))⟩
    exact ⟨by rw [hprv]; exact (hpz _ (hpin j hj)).1, by rw [hk.2]; exact (hpz _ (hpin j hj)).2⟩
  · rw [hpinv] at hpa
    cases hpa
    exact ⟨ha0k j hj, fun hs => hX.a0img j hj (by unfold Slot0 at hs; unfold ShaImg; omega)⟩

set_option maxRecDepth 100000 in
/-- **`main` from its entry to the first operand's `digest_file`** (file-error tier): the loop's
invariant with `ErrMem`, `stderr` untouched. -/
theorem mixed_head {E : Env} {R : ShaRep} {W : World} {b lb kb sr sc : Word} (I : MainImps E W b lb sr)
    (M : MultiImps E R W b lb kb sc) (hopA : E.optindA = lb + 0x204248#64)
    {C : Nat → Prop} {fi : Word} {sti : St} {s : PState} {a0p : Word} {a0 : List Byte}
    {p : Word} {n : List Byte} {rest : List (Word × List Byte)} {g : Word}
    (h : MainEntryF E W b lb kb sr sc C fi sti s a0p a0 (((p, n) :: rest).map Prod.snd) g)
    (ht : FilesEntry E W b lb s ((p, n) :: rest) g) (hX : MixedEntry E W b lb s a0p a0)
    (hnd : ∀ pn ∈ (p, n) :: rest, pn.2.head? ≠ some 0x2d#8) {Q : PState → Prop}
    (k : ∀ v, LoopAt E W b lb kb sr sc s v (s.m.core.read .rsi + 8#64) p n rest [] g →
      ErrMem E W b lb (lb + 0x205378#64) a0 (s.m.core.read .rsp) v.m.memory → v.g.err = s.g.err → MustQ W Q v) :
    MustQ W Q s := by
  have hal := h.abi.aligned
  obtain ⟨hd, hat, hout, hjobs⟩ := h.ghost
  refine sha_main_headP I.img I.hb I.lz I.strrchr I.loc (privKeep E) h.rip h.abi h.room hd h.mem h.rw h.lo h.env
    h.hC h.pinC h.pinK h.lbB h.imgVar h.argsImg h.argv0 h.argv0k h.a0s h.a0k h.a0nz h.noSlash h.guard h.guardk ?_
  intro s1 x hL hpx
  refine sha_main_bufP I.img I.hb I.lz I.atexit I.setvbuf hL (by rw [hL.g]; exact hat) hal h.lo h.hC ?_
  intro y hM hkxy
  have hlen := ht.argcLim
  refine sha_main_getoptP I.img I.hb I.lz I.getopt hM hal h.lo h.hC h.optC h.optK h.optL h.opt
    (args := a0 :: ((p, n) :: rest).map Prod.snd) (by
      rw [ht.argc]; simp only [List.length_cons, List.length_map, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by simp at hlen; omega)) h.argv
    (fun a ha => by
      simp only [List.drop_one, List.tail_cons, List.mem_map] at ha
      obtain ⟨pn, hpn, rfl⟩ := ha
      exact hnd pn hpn) ?_
  intro z hO hkyz
  refine multi_preK I.img I.hb hopA ht hO hout hjobs (by simpa using h.res) ?_
  intro v hv hkzv hKSV hgv
  have hpin : ∀ j, j < 8 → PinR lb ((lb + 0x205378#64).toNat + j) := fun j hj => ⟨by omega, by omega⟩
  have hImgK : ∀ a, ShaImg b a → W.Kept a := fun a ha => Or.inl (by rw [I.img]; exact ha)
  have hpinv : loadN v.m.memory (lb + 0x205378#64) 8 = some a0p := by
    rw [loadN_keeps hkzv (fun j hj => ⟨fun hI => h.pinK _ (hpin j hj) (hImgK _ hI), h.hC _ (h.pinC _ (hpin j hj))⟩),
      loadN_keeps hkyz (fun j hj => ⟨h.pinC _ (hpin j hj), hX.pinOpt _ (hpin j hj)⟩),
      loadN_keeps hkxy (fun j hj => h.pinC _ (hpin j hj))]
    exact hpx
  have hroom : Room W v.m.memory (s.m.core.read .rsp) 4096 := hv.fr.body.room
  refine k v hv (errMem_head M hX h.lo h.hC h.pinC h.pinK h.a0s h.a0k hroom
    (fun a ha => hO.at_.env.np a (Or.inr ⟨h.pinC a ha, hX.pinOpt a ha⟩)) hpinv hkzv hKSV) (by rw [hgv])

set_option maxRecDepth 100000 in
/-- **sha256sum F1 … Fn with refused operands, from `main`'s entry** (on the extended process,
conditional on `Task.okExt` and `Task.errStep`): every run halts with status 0 iff every operand
was read, `stdout` holding the readable operands' lines and `stderr` the diagnostics
`argv[0]: NAME: strerror(e)\n` of the refused ones, in order. -/
theorem sha_main_mixed {E : Env} {R : ShaRep} {W : World} {b lb kb sr sc : Word} (I : MainImps E W b lb sr)
    (M : MultiImps E R W b lb kb sc) (hopA : E.optindA = lb + 0x204248#64) (XO : ExitOk E W b lb)
    {C : Nat → Prop} {fi : Word} {sti : St} {s : PState} {a0p : Word} {a0 : List Byte}
    {ops : List (Word × List Byte)} {g : Word}
    {dat : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.Bytes}
    (h : MainEntryF E W b lb kb sr sc C fi sti s a0p a0 (ops.map Prod.snd) g) (ht : FilesEntry E W b lb s ops g)
    (hX : MixedEntry E W b lb s a0p a0) (hops : ∀ pn ∈ ops, MOp E dat pn.2)
    (Tok : Task.okExt E R W b lb kb sr sc s (ErrMem E W b lb (lb + 0x205378#64) a0 (s.m.core.read .rsp)))
    (Terr : Task.errStep E R W b lb kb sr sc s (ErrMem E W b lb (lb + 0x205378#64) a0 (s.m.core.read .rsp)) a0)
    (x : Silmaril.X86.Str9G.GState) (hx : XG.view x = s.m) :
    MustG XG W (fun z => Ended (if okM E dat a0 ops then 0 else 1) (fun w => w = outsM E dat a0 ops) (z.view XG) ∧
      (z.view XG).g.err = s.g.err ++ errsM E dat a0 ops) ⟨x, s.g⟩ := by
  obtain ⟨p, n, rest, rfl⟩ : ∃ p n rest, ops = (p, n) :: rest := by
    rcases hops' : ops with _ | ⟨⟨p, n⟩, rest⟩
    · exact absurd hops' ht.ne
    · exact ⟨p, n, rest, rfl⟩
  have hnd : ∀ pn ∈ (p, n) :: rest, pn.2.head? ≠ some 0x2d#8 := fun pn hpn => by
    rcases hops pn hpn with h1 | ⟨e, h1⟩
    · exact h1.nd
    · exact h1.nd
  refine mustG_of_mustQ XG hx (mixed_head I M hopA h ht hX hnd fun v hv hE herr => must_done fun x' hx' => ?_)
  have hv' : LoopAtO E W b lb kb sr sc s ((⟨x', v.g⟩ : XPS).view XG) (s.m.core.read .rsi + 8#64) p n rest [] g 1#64 := by
    rw [xview_mk hx']; exact hv
  have hE' : ErrMem E W b lb (lb + 0x205378#64) a0 (s.m.core.read .rsp) ((⟨x', v.g⟩ : XPS).view XG).m.memory := by
    rw [xview_mk hx']; exact hE
  refine Silmaril.X86.RelIsa.Must.mono (fun _ h => h) (fun z hz => ⟨hz.1, ?_⟩)
    (mixed_exitE M XO ⟨h.lo, h.abi.aligned, h.guardk⟩ Tok Terr hv' hE' hops)
  rw [hz.2, xview_mk hx', herr]

end Silmaril.Elf.Link.Dyn.Sha256sum
