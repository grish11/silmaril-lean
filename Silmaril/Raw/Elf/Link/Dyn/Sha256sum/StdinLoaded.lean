module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.StdinMain
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MemDigest
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MemPrint

/-! # GNU `sha256sum`, stdin tier: from the loader relation to the specification

`sha256sum_stdin`: for every `libcrypto.so.3`, `libc.so.6` and `ld.so` agreeing with the pinned
chunks, every base and every ifunc choice, a process started by the kernel on the loaded image
(`ExeLoaded`, `ShaStartState`) ends with the status and standard output of the specification
`Silmaril.Apps.Sha256sum.sha256sum` on the stdin tier (`argv = [a0]`, standard input `data`).

The image facts at `main`'s entry are derived from the loader relation and kept through the
start-up (`sha_reaches_mainA`: `sha_reaches_mainW` with `gate_main'`, so that `main` is entered
with the library's guarantee `World.atMain`, and with the image kept). What is assumed:

* of the world `W` (the library): the imports' contracts (`MainImps`, `TailImps`, `ExitOk`) and,
  at `main`'s entry, `MainLib` (`World.atMain`): the streams, the argument vector `[a0]`, the
  stack, the guard, and the layout of the library's variables against the image and the stack;
* of the kernel: `ShaStartState`.
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
open Silmaril.Elf.Link.Dyn.Imports

theorem shaClr_slotOk : slotOk shaSlots 0x9f68 (.addr 2 0x91400) = true := by decide +kernel

theorem shaBss_plain : plainOk shaFile shaRwPh shaSlots 0xa040 [0#8] = true := by decide +kernel

/-- The image facts of `main`'s tail after loading: `clearerr_unlocked`'s GOT slot, and
`completed.0` (zero-filled `.bss`) is 0 and writable. -/
theorem shaTailMem_of_loaded {Fk Fc Fl : Blob} (hk : ChunksOf Fk cryptoChunks) (hc : ChunksOf Fc libcChunks)
    (hl : ChunksOf Fl ldChunks) {b kb lb ldb res : Word} {ifn : Word → Option Word} {mem : Memory}
    (h : ExeLoaded [shaFile, Fk, Fc, Fl] [b, kb, lb, ldb] ifn false res mem) :
    loadN mem (b + 0x9f68#64) 8 = some (lb + 0x91400#64) ∧ loadN mem (b + 0xa040#64) 1 = some 0#64 ∧
      mem.Permitted .write (b + 0xa040#64).toNat 1 := by
  obtain ⟨f, b', i, D, T, hf, hb, hi, -, hD, hT, himg⟩ := h
  simp only [List.head?_cons, Option.some.injEq] at hf hb
  subst hf hb
  rw [sha_info_f, Option.some.injEq] at hi
  subst hi
  rw [sha_slots hk hc hl, Option.some.injEq] at hD
  subst hD
  have hrw : shaRwPh ∈ shaInfo.phs := by decide
  refine ⟨himg.loadSlot hT hrw rfl (by decide) (by decide) (by decide) shaClr_slotOk (by rfl), ?_, ?_⟩
  · have := himg.readPlain (l := [0#8]) hT hrw rfl (by decide) (by decide) (by decide) (acc := .read) rfl shaBss_plain
    have h1 : mem.readBytes (b + 0xa040#64).toNat 1 = some [0#8] := this
    simp only [loadN, h1]
    rfl
  · have hrel : Silmaril.Elf.Link.Dyn.inRelro shaInfo 0xa040 = false := by decide +kernel
    obtain ⟨hwrap, -, -, hw, -⟩ := himg shaRwPh hrw rfl 0xa040 (by simp [shaRwPh]) (by simp [shaRwPh])
    dsimp only at hwrap hw
    rw [Memory.Permitted, Memory.checkSpan_iff]
    simp only [Silmaril.Process.addressLimit]
    have e : (b + 0xa040#64).toNat = b.toNat + 0xa040 := addr_toNat hwrap
    refine ⟨by rw [e]; omega, by rw [e]; omega, fun k hk => ?_⟩
    have hk0 : k = 0 := by omega
    subst hk0
    rw [Nat.add_zero, hw]
    simp [hrel, shaRwPh]

/-- All image facts of `main` and its helpers after loading (`sr`, `sc`: the `strrchr` and
`strcspn` ifunc choices). -/
theorem shaMemAll_of_loaded {Fk Fc Fl : Blob} (hk : ChunksOf Fk cryptoChunks) (hc : ChunksOf Fc libcChunks)
    (hl : ChunksOf Fl ldChunks) {b kb lb ldb res sr sc : Word} {ifn : Word → Option Word} {mem : Memory}
    (hsr : ifn (lb + 0xb5210#64) = some sr) (hsc : ifn (lb + 0xb4410#64) = some sc)
    (h : ExeLoaded [shaFile, Fk, Fc, Fl] [b, kb, lb, ldb] ifn false res mem) : ShaMemAll b lb kb sr sc mem :=
  ⟨shaMem_of_loaded hk hc hl h, shaMemC_of_loaded hk hc hl h, shaMemD_of_loaded hk hc hl h,
    shaMemP_of_loaded hk hc hl hsc h, shaMemM_of_loaded hk hc hl hsr h⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`sha256sum` reaches `main`** (`sha_reaches_mainW`), entered with the library's guarantee
`World.atMain` and with the image kept since the kernel's entry state. -/
theorem sha_reaches_mainAE {b lb : Word} {W : World} (E : ShaWorldOk W b lb) {Q : PState → Prop}
    {s : PState} {argc : Word} (hm : ShaMem b lb s.m.memory)
    (hs : ShaStartState W b s argc)
    (k : ∀ t, SCb W b lb t (b + 0x2750#64) → t.g.jobs = [.exitRax] →
      t.g.out = [] → t.g.atexit = [] → Keeps (ShaImg b) s.m.memory t.m.memory →
      (t.g.allocs = 0 ∧ t.g.heap = 0 ∧ t.g.files = 0) → W.atMain t → t.g.err = [] → MustQ W Q t) :
    MustQ W Q s := by
  have hd0 : s.g.done = none := by rw [hs.ghost]
  have hgo : ¬ W.InImage W.gate.toNat := by
    rw [E.img]; exact E.gate_out
  refine sha_startW E.img E.hb hd0 hm hs.rip hs.al hs.room hs.argc ?_
  intro t1 hg1 hrip1 hm1 hk1 habi1 hrdi1 hrsi1 hrdx1
  have hd1 : t1.g.done = none := by rw [hg1]; exact hd0
  -- __libc_start_main
  refine must_fn hd1 (by rw [hrip1, E.img]; exact E.lsm_out)
    (by rw [hrip1]; exact Ne.symm E.gate_lsm) E.lz (f := .libcStartMain)
    (by rw [hrip1]; exact E.lsm) (fun r => Iff.rfl) habi1 ?_
  rintro t2 ⟨⟨hrip2, hk2, -⟩, hg2⟩
  have hm2 := hm1.keep E.hb (skeepsImgW E.img hk2)
  simp only [E.inits, List.map_cons, List.map_nil, List.cons_append, List.nil_append, hrdi1] at hg2
  have hd2 : t2.g.done = none := by rw [hg2]; exact hd1
  -- _init
  refine gate_call hd2 (by rw [hrip2]; exact hgo) hrip2 (by rw [hg2]) ?_
  intro t3 he3 _ _ _ hg3
  have hd3 : t3.g.done = none := by rw [hg3]; exact hd2
  have hm3 := hm2.keep E.hb (skeepsImgW E.img he3.2.2.2.2.1)
  refine sha_initW E.img E.hb (scb_of_entersW E.img E.hb he3 hm2 hd3) ?_
  intro u3 hru3 hgu3 hmu3
  have hdu3 : u3.g.done = none := by rw [hgu3]; exact hd3
  -- frame_dummy
  refine gate_call hdu3 (by rw [hru3]; exact hgo) hru3 (by rw [hgu3, hg3]) ?_
  intro t4 he4 _ _ _ hg4
  have hd4 : t4.g.done = none := by rw [hg4]; exact hdu3
  have hm4 := (hmu3 ▸ hm3).keep E.hb (skeepsImgW E.img he4.2.2.2.2.1)
  refine sha_frameDummyW E.img E.hb (scb_of_entersW E.img E.hb he4 (hmu3 ▸ hm3) hd4) ?_
  intro u4 hru4 hgu4 hmu4
  have hdu4 : u4.g.done = none := by rw [hgu4]; exact hd4
  refine gate_main' hdu4 (by rw [hru4]; exact hgo) hru4 (by rw [hgu4, hg4]) ?_
  intro t5 he5 _ _ _ hg5 hat5
  have hd5 : t5.g.done = none := by rw [hg5]; exact hdu4
  have hK : Keeps (ShaImg b) s.m.memory t5.m.memory :=
    (((hk1.trans (skeepsImgW E.img hk2)).trans (skeepsImgW E.img he3.2.2.2.2.1)).trans
      (hmu3 ▸ skeepsImgW E.img he4.2.2.2.2.1)).trans (hmu4 ▸ skeepsImgW E.img he5.2.2.2.2.1)
  refine k t5 (scb_of_entersW E.img E.hb he5 (hmu4 ▸ hm4) hd5) (by rw [hg5]) ?_ ?_ hK ?_ hat5 ?_
  · rw [hg5, hgu4, hg4, hgu3, hg3, hg2, hg1, hs.ghost]
  · rw [hg5, hgu4, hg4, hgu3, hg3, hg2, hg1, hs.ghost]
  · rw [hg5, hgu4, hg4, hgu3, hg3, hg2, hg1, hs.ghost]; exact ⟨rfl, rfl, rfl⟩
  · rw [hg5, hgu4, hg4, hgu3, hg3, hg2, hg1, hs.ghost]

/-- **From the kernel's start state to `main`'s entry** (`sha_reaches_mainAE` without `stderr`). -/
theorem sha_reaches_mainA {b lb : Word} {W : World} (E : ShaWorldOk W b lb) {Q : PState → Prop}
    {s : PState} {argc : Word} (hm : ShaMem b lb s.m.memory)
    (hs : ShaStartState W b s argc)
    (k : ∀ t, SCb W b lb t (b + 0x2750#64) → t.g.jobs = [.exitRax] →
      t.g.out = [] → t.g.atexit = [] → Keeps (ShaImg b) s.m.memory t.m.memory →
      (t.g.allocs = 0 ∧ t.g.heap = 0 ∧ t.g.files = 0) → W.atMain t → MustQ W Q t) :
    MustQ W Q s :=
  sha_reaches_mainAE E hm hs fun t h1 h2 h3 h4 h5 h6 h7 _ => k t h1 h2 h3 h4 h5 h6 h7

/-- **What the library and the kernel guarantee at `main`'s entry `t`** on the stdin tier (the
part of `MainEntryS` and `TailEntry` that is not about the image): the stack's bound, the
streams (`stdout`, `stderr` fresh; `stdin` = `fi` holding `data`), the argument vector `[a0]`
(`argc = 1`, `argv[1]`'s slot), the guard, and where the library's variables lie. -/
structure MainLib (E : Env) (W : World) (b lb : Word) (C : Nat → Prop) (fi : Word) (t : PState)
    (a0p : Word) (a0 data : List Byte) (g : Word) : Prop where
  lo : E.S.lo + 4096 ≤ (t.m.core.read .rsp).toNat
  env : MEnv E W b lb C fi (outSt 1) (outSt 2) (stdinSt data) t.m.memory
  hC : ∀ a, C a → a < (t.m.core.read .rsp).toNat - 4096 ∨ (t.m.core.read .rsp).toNat + 8 ≤ a
  pinC : ∀ a, PinR lb a → C a
  pinK : ∀ a, PinR lb a → ¬ W.Kept a
  optC : ∀ a, OptR E a → C a
  optK : ∀ a, OptR E a → ¬ W.Kept a
  optL : ∀ a, OptR E a → a + 48 < (t.m.core.read .rsp).toNat
  opt : E.optindA.toNat + 4 < 2 ^ 64
  lbB : lb.toNat + 0x2056b0 < 2 ^ 64
  imgVar : ∀ a, ShaImg b a → ¬ VarR lb a
  argsImg : ∀ a, W.args a → ¬ ShaImg b a
  argc : BitVec.setWidth 32 (t.m.core.read .rdi) = 1#32
  argv : ∀ m, Keeps W.args t.m.memory m → Argv m (t.m.core.read .rsi) [a0]
  argv0 : loadN t.m.memory (t.m.core.read .rsi) 8 = some a0p
  argv0k : ∀ k, k < 8 → W.Kept ((t.m.core.read .rsi).toNat + k)
  a0s : CStr t.m.memory a0p a0
  a0k : ∀ j, j < a0.length + 1 → W.Kept (a0p.toNat + j)
  a0nz : a0p ≠ 0#64
  noSlash : ∀ x ∈ a0, x ≠ 0x2f#8
  guard : loadN t.m.memory (t.m.core.fsBase + 0x28#64) 8 = some g
  guardk : ∀ j, j < 8 → W.Kept ((t.m.core.fsBase + 0x28#64).toNat + j)
  guardImg : ∀ j, j < 8 → ¬ ShaImg b ((t.m.core.fsBase + 0x28#64).toNat + j)
  var : loadN t.m.memory (lb + 0x2056b0#64) 8 = some fi
  vark : ∀ j, j < 8 → W.Kept ((lb + 0x2056b0#64).toNat + j)
  varImg : ∀ j, j < 8 → ¬ ShaImg b ((lb + 0x2056b0#64).toNat + j)
  fi0 : fi ≠ 0#64
  fiO : fi ≠ E.stdoutF
  fiE : fi ≠ E.stderrF
  avHi : (t.m.core.read .rsp).toNat + 8 ≤ (t.m.core.read .rsi).toNat
  av : (t.m.core.read .rsi).toNat + 16 < 2 ^ 64
  avA : ∀ j, j < 8 → W.args ((t.m.core.read .rsi).toNat + 8 + j)
  avR : t.m.memory.Permitted .read ((t.m.core.read .rsi).toNat + 8) 8
  avW : t.m.memory.Permitted .write ((t.m.core.read .rsi).toNat + 8) 8
  avVar : ∀ j, j < 8 → ¬ VarR lb ((t.m.core.read .rsi).toNat + 8 + j)
  avIn : (lb + 0x2056b0#64).toNat + 8 ≤ (t.m.core.read .rsi).toNat + 8 ∨
    (t.m.core.read .rsi).toNat + 16 ≤ (lb + 0x2056b0#64).toNat
  avG : (t.m.core.fsBase + 0x28#64).toNat + 8 ≤ (t.m.core.read .rsi).toNat + 8 ∨
    (t.m.core.read .rsi).toNat + 16 ≤ (t.m.core.fsBase + 0x28#64).toNat

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **GNU `sha256sum`, stdin tier, from the loader relation to the specification**: for every
`libcrypto.so.3`, `libc.so.6` and `ld.so` agreeing with the pinned chunks, every base, every
ifunc choice (`sr`, `sc`: those of `strrchr` and `strcspn`) and binding mode, a process started
by the kernel on the loaded image, in a world with the imports' contracts (`MainImps`,
`TailImps`, `ExitOk`) whose library enters `main` with `argv = [a0]` and standard input `data`
(`MainLib`, via `World.atMain`), ends with the specification's exit status and standard output
(`Silmaril.Apps.Sha256sum.sha256sum` on `stdinWorld a0 data`). -/
theorem sha256sum_stdin {Fk Fc Fl : Blob} (hk : ChunksOf Fk cryptoChunks) (hc : ChunksOf Fc libcChunks)
    (hl : ChunksOf Fl ldChunks) {b kb lb ldb res sr sc : Word} {ifn : Word → Option Word} {lazy : Bool}
    (hsr : ifn (lb + 0xb5210#64) = some sr) (hsc : ifn (lb + 0xb4410#64) = some sc)
    {E : Env} {R : ShaRep} {W : World} (I : MainImps E W b lb sr) (T : TailImps E R W b lb kb sc)
    (XO : ExitOk E W b lb) {s : PState} {argc : Word}
    (hload : ExeLoaded [shaFile, Fk, Fc, Fl] [b, kb, lb, ldb] ifn lazy res s.m.memory)
    (hs : ShaStartState W b s argc)
    (hR : 1 ≤ E.maxAllocs ∧ 0x8048 ≤ E.maxHeap) {a0 data : List Byte}
    (hA : ∀ t, W.atMain t → ∃ C fi a0p g, MainLib E W b lb C fi t a0p a0 data g) (posix : Bool)
    (fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult) :
    MustQ W (Ended (Silmaril.Apps.Sha256sum.sha256sum (stdinWorld a0 data posix fs)).status fun w =>
      w = (Silmaril.Apps.Sha256sum.sha256sum (stdinWorld a0 data posix fs)).stdout.map UInt8.toBitVec ∧
      (Silmaril.Apps.Sha256sum.sha256sum (stdinWorld a0 data posix fs)).stderr = []) s := by
  have := sha_not_lazy hload
  subst this
  have hb := XO.wo.hb
  refine sha_reaches_mainA XO.wo (shaMem_of_loaded hk hc hl hload) hs ?_
  intro t hC hj ho ha hK hcnt hat
  obtain ⟨C, fi, a0p, g, L⟩ := hA t hat
  obtain ⟨hclr, hbss, hbssw⟩ := shaTailMem_of_loaded hk hc hl hload
  have hrw0 := shaRw_of_loaded hload
  have hI : ∀ n, n < 0xa188 → ∀ j, j < 8 → n + j < 0xa188 → ShaImg b ((b + BitVec.ofNat 64 n).toNat + j) :=
    fun n hn j hj hnj => by rw [addr_toNat (by omega)]; exact ⟨by omega, by omega⟩
  refine sha_main_stdin_spec_ok I T XO (C := C) (fi := fi) (a0p := a0p) (g := g)
    ⟨hC.rip, Silmaril.Elf.Link.Dyn.Hello.abiEntry_of hC.al hC.ret, hC.room, ⟨hC.done, ha, ho, hj⟩,
      (shaMemAll_of_loaded hk hc hl hsr hsc hload).keep hb hK, fun j hj => ?_, L.lo, L.env, L.hC, L.pinC,
      L.pinK, L.optC, L.optK, L.optL, L.opt, L.lbB, L.imgVar, L.argsImg, L.argc, L.argv, L.argv0, L.argv0k,
      L.a0s, L.a0k, L.a0nz, L.noSlash, L.guard, L.guardk, by rw [hcnt.1, hcnt.2.1]; omega⟩
    ⟨hC.ret, hC.al, L.lo, (shaMainAll_of_loaded hk hc hl hload).keepW hb (imgW_img hK),
      by rw [loadN_keeps hK (fun j hj => hI 0x9f68 (by decide) j hj (by omega))]; exact hclr,
      by rw [loadN_keeps hK (fun j hj => hI 0xa040 (by decide) j (by omega) (by omega))]; exact hbss,
      (hK.permitted (fun j hj => hI 0xa040 (by decide) j (by omega) (by omega))).2 hbssw,
      L.var, L.vark, L.varImg, L.fi0, L.fiO, L.fiE, L.guard, L.guardk, L.guardImg, L.imgVar, L.argsImg, L.optK,
      L.avHi, L.av, L.avA, L.avR, L.avW, L.avVar, L.avIn, L.avG⟩ posix fs
  have hj' : ShaImg b (b.toNat + 0xa160 + j) := ⟨by omega, by omega⟩
  rw [(hK _ hj').2, (hK _ hj').2]
  exact hrw0 j hj

end Silmaril.Elf.Link.Dyn.Sha256sum
