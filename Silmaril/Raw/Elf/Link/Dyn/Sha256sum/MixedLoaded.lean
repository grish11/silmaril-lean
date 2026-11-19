module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MixedSpec
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MixedErr
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MultiLoaded

/-! # GNU `sha256sum F1 … Fn` with refused operands: from the loader relation to the specification

`sha256sum_mixed_loaded` (the mirror of `MultiLoaded.sha256sum_files` for the file-error tier):
for every `libcrypto.so.3`, `libc.so.6` and `ld.so` agreeing with the pinned chunks, every
page-aligned base (`ExeLoadedP`), every ifunc choice and binding mode, a process started by the
kernel on the loaded image, run on the extended process (`procG XG W`: the image machine with
SSE moves, which `quotef` needs), halts with the exit status, standard output and standard error
of `Silmaril.Apps.Sha256sum.sha256sum` on `argv = a0 :: names`, each name readable and printed
verbatim or refused at `open` and shown bare (`MOp`). Unconditional: a readable operand keeps
`program_invocation_name` (`MixedLoop.task_midPin`), a refused operand is
`MixedErr.task_errStep`, given `error`'s and `__errno_location`'s contracts (`ErrImps`) and
`errno` below the streams.

From the loader (PROVED here): gnulib's quoting slots as loaded (`qslots_of_loaded`) and
`slot0`'s permissions (`slot0_of_loaded`); `ShaRO` and `ShaMemK` (the GOT and `%s`). Assumed
of the world: `quotef`'s imports (`QImps`), and at `main`'s entry, besides `MainLibF`, where
`program_invocation_name` and `argv[0]` lie (`MixedLib`).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Link (Blob)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.ProcG
open Silmaril.Elf.Link.Dyn.Streams
open Silmaril.Elf.Link.Dyn.Imports

theorem shaQ_plain : plainOk shaFile shaRwPh shaSlots 0xa010 [1#8, 0#8, 0#8, 0#8] = true ∧
    plainOk shaFile shaRwPh shaSlots 0xa020 [0#8, 1#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8] = true := by
  decide +kernel

theorem shaQS_slotsOk : slotOk shaSlots 0xa028 (.addr 0 0xa060) = true ∧
    slotOk shaSlots 0xa030 (.addr 0 0xa020) = true := by decide +kernel

set_option maxRecDepth 20000 in
/-- **gnulib's quoting slots as loaded**: one slot, `slotvec = &slotvec0`, `slotvec0 = {256, slot0}`. -/
theorem qslots_of_loaded {Fk Fc Fl : Blob} (hk : ChunksOf Fk cryptoChunks) (hc : ChunksOf Fc libcChunks)
    (hl : ChunksOf Fl ldChunks) {b kb lb ldb res : Word} {ifn : Word → Option Word} {mem : Memory}
    (h : ExeLoaded [shaFile, Fk, Fc, Fl] [b, kb, lb, ldb] ifn false res mem) : QSlots b mem := by
  obtain ⟨f, b', i, D, T, hf, hb, hi, -, hD, hT, himg⟩ := h
  simp only [List.head?_cons, Option.some.injEq] at hf hb
  subst hf hb
  rw [sha_info_f, Option.some.injEq] at hi
  subst hi
  rw [sha_slots hk hc hl, Option.some.injEq] at hD
  subst hD
  have hrw : shaRwPh ∈ shaInfo.phs := by decide
  obtain ⟨p1, p2⟩ := shaQ_plain
  obtain ⟨s1, s2⟩ := shaQS_slotsOk
  refine ⟨?_, ?_, himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s1 (by rfl),
    himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) s2 (by rfl)⟩
  · have := himg.readPlain (l := [1#8, 0#8, 0#8, 0#8]) hT hrw rfl (by decide) (by decide) (by decide)
      (acc := .read) rfl p1
    have h1 : mem.readBytes (b + 0xa010#64).toNat 4 = some [1#8, 0#8, 0#8, 0#8] := this
    simp only [loadN, h1]
    rfl
  · have := himg.readPlain (l := [0#8, 1#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8]) hT hrw rfl (by decide) (by decide)
      (by decide) (acc := .read) rfl p2
    have h1 : mem.readBytes (b + 0xa020#64).toNat 8 = some [0#8, 1#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8] := this
    simp only [loadN, h1]
    rfl

/-- **`slot0` is readable and writable after loading** (`.bss`, outside RELRO). -/
theorem slot0_of_loaded {Fk Fc Fl : Blob} {b kb lb ldb res : Word} {ifn : Word → Option Word} {mem : Memory}
    (h : ExeLoaded [shaFile, Fk, Fc, Fl] [b, kb, lb, ldb] ifn false res mem) :
    ∀ a, Slot0 b a → mem.permits .read a = true ∧ mem.permits .write a = true := by
  obtain ⟨f, b', i, D, T, hf, hb, hi, -, hD, hT, himg⟩ := h
  simp only [List.head?_cons, Option.some.injEq] at hf hb
  subst hf hb
  rw [sha_info_f, Option.some.injEq] at hi
  subst hi
  have hrw : shaRwPh ∈ shaInfo.phs := by decide
  have hrel : ∀ k, k < 0x100 → Silmaril.Elf.Link.Dyn.inRelro shaInfo (0xa060 + k) = false := by
    decide +kernel
  intro a ha
  unfold Slot0 at ha
  obtain ⟨hwrap, hr, -, hw, -⟩ := himg shaRwPh hrw rfl (0xa060 + (a - b.toNat - 0xa060))
    (by simp [shaRwPh]; omega) (by simp [shaRwPh]; omega)
  dsimp only at hwrap hr hw
  rw [addr_toNat hwrap, ← Nat.add_assoc] at hr hw
  have e : b.toNat + 0xa060 + (a - b.toNat - 0xa060) = a := by omega
  rw [e] at hr hw
  refine ⟨by rw [hr]; simp [shaRwPh], ?_⟩
  rw [hw]
  simp [hrel (a - b.toNat - 0xa060) (by omega), shaRwPh]

/-- **Where the library leaves `program_invocation_name` and `argv[0]`** at `main`'s entry `t`
(the refused path's part of the library's guarantee, beside `MainLibF`). -/
structure MixedLib (E : Env) (W : World) (b lb : Word) (t : PState) (a0p : Word) (a0 : List Byte) : Prop where
  pinOpt : ∀ a, PinR lb a → ¬ OptR E a
  pinLo : ∀ j, j < 8 → (lb + 0x205378#64).toNat + j < E.S.lo ∨
    (t.m.core.read .rsp).toNat + 8 ≤ (lb + 0x205378#64).toNat + j
  a0img : ∀ j, j < a0.length + 1 → ¬ ShaImg b (a0p.toNat + j)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **GNU `sha256sum F1 … Fn` with refused operands, from the loader relation to the
specification**: every run of
the extended process from the kernel's start state halts with the specification's exit status
(0 iff every operand was read), standard output (the readable operands' records) and standard
error (`argv[0]: NAME: strerror(e)\n` per refused operand), in order. -/
theorem sha256sum_mixed_loaded {Fk Fc Fl : Blob} (hk : ChunksOf Fk cryptoChunks) (hc : ChunksOf Fc libcChunks)
    (hl : ChunksOf Fl ldChunks) {b kb lb ldb res sr sc : Word} {ifn : Word → Option Word} {lazy : Bool}
    (hsr : ifn (lb + 0xb5210#64) = some sr) (hsc : ifn (lb + 0xb4410#64) = some sc)
    {E : Env} {R : ShaRep} {W : World} (I : MainImps E W b lb sr) (M : MultiImps E R W b lb kb sc)
    (hopA : E.optindA = lb + 0x204248#64) (XO : ExitOk E W b lb) {s : PState} {argc : Word}
    (hload : ExeLoadedP [shaFile, Fk, Fc, Fl] [b, kb, lb, ldb] ifn lazy res s.m.memory)
    (hs : ShaStartState W b s argc) (QI : QImps E W b lb s.m.memory) {a0 : List Byte} {names : List (List Byte)}
    (hA : ∀ t, W.atMain t → ∃ C fi sti a0p g ops, ops.map Prod.snd = names ∧
      MainLibF E W b lb C fi sti t a0p a0 ops g ∧ MixedLib E W b lb t a0p a0)
    {dat : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.Bytes}
    (hR : names.length ≤ E.maxAllocs ∧ 0x8048 * names.length ≤ E.maxHeap ∧ names.length ≤ E.maxOpen)
    (hops : ∀ n ∈ names, MOp E dat n) (hne : ∀ n ∈ names, n ≠ []) (posix : Bool)
    (stdin : Silmaril.Apps.Sha256sum.Stdin)
    (K : ErrImps E W lb (lb + 0x205378#64)) (herrLo : E.errnoA.toNat + 4 ≤ E.S.lo)
    (x : Silmaril.X86.Str9G.GState) (hx : XG.view x = s.m) :
    MustG XG W (fun z =>
      Ended (Silmaril.Apps.Sha256sum.sha256sum (filesWorldN a0 names posix E.fs stdin)).status (fun out =>
        out = (Silmaril.Apps.Sha256sum.sha256sum (filesWorldN a0 names posix E.fs stdin)).stdout.map UInt8.toBitVec)
        (z.view XG) ∧
      (z.view XG).g.err =
        (Silmaril.Apps.Sha256sum.sha256sum (filesWorldN a0 names posix E.fs stdin)).stderr.map UInt8.toBitVec)
      ⟨x, s.g⟩ := by
  have hload' := hload.1
  have := sha_not_lazy hload'
  subst this
  have hb := XO.wo.hb
  refine mustG_of_mustQ XG hx (sha_reaches_mainAE XO.wo (shaMem_of_loaded hk hc hl hload') hs ?_)
  intro t hC hj ho ha hK hcnt hat herr
  refine must_done fun x' hx' => ?_
  obtain ⟨C, fi, sti, a0p, g, ops, rfl, L, LX⟩ := hA t hat
  obtain ⟨-, hbss, hbssw⟩ := shaTailMem_of_loaded hk hc hl hload'
  have hhr := shaHr_of_loaded hk hc hl hload'
  have hrw0 := shaRw_of_loaded hload'
  have hI : ∀ n, n < 0xa188 → ∀ j, j < 8 → n + j < 0xa188 → ShaImg b ((b + BitVec.ofNat 64 n).toNat + j) :=
    fun n hn j hj hnj => by rw [addr_toNat (by omega)]; exact ⟨by omega, by omega⟩
  have hS0 := slot0_of_loaded hload'
  have hX : MixedEntry E W b lb t a0p a0 := by
    refine ⟨(shaMemK_of_loaded hk hc hl hload').keep hb hK,
      ⟨Fk, Fc, Fl, kb, ldb, res, ifn, s.m.memory, hk, hc, hl, hload', hK.mono fun a ha => ⟨by omega, by omega⟩⟩,
      QI.keep (hK.mono fun a ha => ha.1), (qslots_of_loaded hk hc hl hload').keep hb (hK.mono fun a ha => ha.1),
      fun a ha => ?_, LX.pinOpt, LX.pinLo, LX.a0img⟩
    have hi : ShaImg b a := by unfold Slot0 at ha; unfold ShaImg; omega
    rw [(hK a hi).2, (hK a hi).2]
    exact hS0 a ha
  have hEF : MainEntryF E W b lb kb sr sc C fi sti t a0p a0 (ops.map Prod.snd) g := by
    refine ⟨hC.rip, Silmaril.Elf.Link.Dyn.Hello.abiEntry_of hC.al hC.ret, hC.room, ⟨hC.done, ha, ho, hj⟩,
      (shaMemAll_of_loaded hk hc hl hsr hsc hload').keep hb hK, fun j hj => ?_, L.lo, L.env, L.hC, L.pinC,
      L.pinK, L.optC, L.optK, L.optL, L.opt, L.lbB, L.imgVar, L.argsImg, L.argv, L.argv0, L.argv0k,
      L.a0s, L.a0k, L.a0nz, L.noSlash, L.guard, L.guardk,
      ⟨⟨[], hj⟩, by rw [hcnt.1]; simpa using hR.1, by rw [hcnt.2.1]; simpa using hR.2.1,
        by rw [hcnt.2.2]; simpa using hR.2.2⟩⟩
    have hj' : ShaImg b (b.toNat + 0xa160 + j) := ⟨by omega, by omega⟩
    rw [(hK _ hj').2, (hK _ hj').2]
    exact hrw0 j hj
  have hFE : FilesEntry E W b lb t ops g :=
    ⟨hC.ret, hC.al, L.lo, (shaMainAll_of_loaded hk hc hl hload').keepW hb (imgW_img hK),
      by rw [loadN_keeps hK (fun j hj => hI 0xa040 (by decide) j (by omega) (by omega))]; exact hbss,
      (hK.permitted (fun j hj => hI 0xa040 (by decide) j (by omega) (by omega))).2 hbssw,
      by rw [loadN_keeps hK (fun j hj => hI 0xa160 (by decide) j (by omega) (by omega))]; exact hhr,
      L.guard, L.guardk, L.guardImg, L.imgVar, L.argsImg, L.optK, L.args, L.ne, L.argc, L.argcLim, L.avLim⟩
  have hmain := sha_main_mixed_spec I M hopA XO hEF hFE hX (fun pn hpn => hops pn.2 (List.mem_map_of_mem hpn))
    (fun pn hpn => hne pn.2 (List.mem_map_of_mem hpn)) posix stdin (task_okExt task_midPin)
    (task_errStep K hload.2.mod16 herrLo L.argsImg L.guardImg L.imgVar (fun j hj hi =>
      L.pinK ((lb + 0x205378#64).toNat + j) ⟨by omega, by omega⟩ (Or.inl (by rw [M.dig.cl.img]; exact hi)))) x' hx'
  rw [← filesWorld_names]
  refine Silmaril.X86.RelIsa.Must.mono (fun _ h => h) ?_ hmain
  intro z hz
  exact ⟨hz.1, by rw [hz.2, herr, List.nil_append]⟩

end Silmaril.Elf.Link.Dyn.Sha256sum
