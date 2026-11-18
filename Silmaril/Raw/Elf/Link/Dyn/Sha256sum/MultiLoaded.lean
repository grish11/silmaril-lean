module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MultiMain
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.StdinLoaded

/-! # GNU `sha256sum FILE1 … FILEn`, success tier: from the loader relation to the specification

`sha256sum_files`: for every `libcrypto.so.3`, `libc.so.6` and `ld.so` agreeing with the pinned
chunks, every base and every ifunc choice, a process started by the kernel on the loaded image
(`ExeLoaded`, `ShaStartState`) ends with the status and standard output of the specification
`Silmaril.Apps.Sha256sum.sha256sum` on `argv = a0 :: names` (`n ≥ 1` operands), when every
operand is a readable file whose name is printed verbatim (`OpOk`, non-empty). The mirror of
`StdinLoaded.sha256sum_stdin`.

The image facts at `main`'s entry come from the loader relation, kept through the start-up
(`sha_reaches_mainA`); `have_read_stdin = 0` is the zero-filled `.bss` (`shaHr_plain`). What is
assumed: of the world `W` (the library), the imports' contracts (`MainImps`, `MultiImps`,
`ExitOk`, `optind`'s address) and, at `main`'s entry, `MainLibF` (via `World.atMain`); of the
kernel, `ShaStartState`.
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

theorem shaHr_plain : plainOk shaFile shaRwPh shaSlots 0xa160 [0#8] = true := by decide +kernel

/-- `have_read_stdin` (zero-filled `.bss`) is 0 after loading. -/
theorem shaHr_of_loaded {Fk Fc Fl : Blob} (hk : ChunksOf Fk cryptoChunks) (hc : ChunksOf Fc libcChunks)
    (hl : ChunksOf Fl ldChunks) {b kb lb ldb res : Word} {ifn : Word → Option Word} {mem : Memory}
    (h : ExeLoaded [shaFile, Fk, Fc, Fl] [b, kb, lb, ldb] ifn false res mem) :
    loadN mem (b + 0xa160#64) 1 = some 0#64 := by
  obtain ⟨f, b', i, D, T, hf, hb, hi, -, hD, hT, himg⟩ := h
  simp only [List.head?_cons, Option.some.injEq] at hf hb
  subst hf hb
  rw [sha_info_f, Option.some.injEq] at hi
  subst hi
  rw [sha_slots hk hc hl, Option.some.injEq] at hD
  subst hD
  have hrw : shaRwPh ∈ shaInfo.phs := by decide
  have := himg.readPlain (l := [0#8]) hT hrw rfl (by decide) (by decide) (by decide) (acc := .read) rfl shaHr_plain
  have h1 : mem.readBytes (b + 0xa160#64).toNat 1 = some [0#8] := this
  simp only [loadN, h1]
  rfl

/-- **What the library and the kernel guarantee at `main`'s entry `t`** on the file tier (the
part of `MainEntryF` and `FilesEntry` that is not about the image): the stack's bound, the
streams (`stdout`, `stderr` fresh; `stdin` = `fi` in some state), the argument vector
`a0 :: ops` (`argc = |ops| + 1`, the operands' slots and names in the argument area), the guard,
and where the library's variables lie. -/
structure MainLibF (E : Env) (W : World) (b lb : Word) (C : Nat → Prop) (fi : Word) (sti : St) (t : PState)
    (a0p : Word) (a0 : List Byte) (ops : List (Word × List Byte)) (g : Word) : Prop where
  lo : E.S.lo + 4096 ≤ (t.m.core.read .rsp).toNat
  env : MEnv E W b lb C fi (outSt 1) (outSt 2) sti t.m.memory
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
  argv : ∀ m, Keeps W.args t.m.memory m → Argv m (t.m.core.read .rsi) (a0 :: ops.map Prod.snd)
  argv0 : loadN t.m.memory (t.m.core.read .rsi) 8 = some a0p
  argv0k : ∀ k, k < 8 → W.Kept ((t.m.core.read .rsi).toNat + k)
  a0s : CStr t.m.memory a0p a0
  a0k : ∀ j, j < a0.length + 1 → W.Kept (a0p.toNat + j)
  a0nz : a0p ≠ 0#64
  noSlash : ∀ x ∈ a0, x ≠ 0x2f#8
  guard : loadN t.m.memory (t.m.core.fsBase + 0x28#64) 8 = some g
  guardk : ∀ j, j < 8 → W.Kept ((t.m.core.fsBase + 0x28#64).toNat + j)
  guardImg : ∀ j, j < 8 → ¬ ShaImg b ((t.m.core.fsBase + 0x28#64).toNat + j)
  args : ArgsAt W t.m.memory (t.m.core.read .rsi + 8#64) ops
  ne : ops ≠ []
  argc : BitVec.setWidth 32 (t.m.core.read .rdi) = BitVec.ofNat 32 (ops.length + 1)
  argcLim : ops.length + 1 < 2 ^ 31
  avLim : (t.m.core.read .rsi).toNat + 8 * (ops.length + 1) < 2 ^ 64

/-- The specification world of a file-tier run, by names. -/
def filesWorldN (a0 : List Byte) (names : List (List Byte)) (posix : Bool)
    (fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult)
    (stdin : Silmaril.Apps.Sha256sum.Stdin) : Silmaril.Apps.Sha256sum.World :=
  { argv := toSpec a0 :: names.map toSpec, posix, fs, stdin }

theorem filesWorld_names (a0 : List Byte) (ops : List (Word × List Byte)) (posix : Bool)
    (fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult)
    (stdin : Silmaril.Apps.Sha256sum.Stdin) :
    filesWorld a0 ops posix fs stdin = filesWorldN a0 (ops.map Prod.snd) posix fs stdin := by
  simp [filesWorld, filesWorldN, List.map_map, Function.comp_def]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **GNU `sha256sum FILE1 … FILEn`, success tier, from the loader relation to the
specification**: for every `libcrypto.so.3`, `libc.so.6` and `ld.so` agreeing with the pinned
chunks, every base, every ifunc choice (`sr`, `sc`: those of `strrchr` and `strcspn`) and
binding mode, a process started by the kernel on the loaded image, in a world with the imports'
contracts (`MainImps`, `MultiImps`, `ExitOk`) whose library enters `main` with
`argv = a0 :: names` (`MainLibF`, via `World.atMain`), every name non-empty, not starting with
`-`, without backslash, LF or CR, and a file that opens and reads without error (`OpOk`), ends
with the specification's exit status and standard output (`Silmaril.Apps.Sha256sum.sha256sum`
on `filesWorldN a0 names`), whose standard error is empty. -/
theorem sha256sum_files {Fk Fc Fl : Blob} (hk : ChunksOf Fk cryptoChunks) (hc : ChunksOf Fc libcChunks)
    (hl : ChunksOf Fl ldChunks) {b kb lb ldb res sr sc : Word} {ifn : Word → Option Word} {lazy : Bool}
    (hsr : ifn (lb + 0xb5210#64) = some sr) (hsc : ifn (lb + 0xb4410#64) = some sc)
    {E : Env} {R : ShaRep} {W : World} (I : MainImps E W b lb sr) (M : MultiImps E R W b lb kb sc)
    (hopA : E.optindA = lb + 0x204248#64) (XO : ExitOk E W b lb) {s : PState} {argc : Word}
    (hload : ExeLoaded [shaFile, Fk, Fc, Fl] [b, kb, lb, ldb] ifn lazy res s.m.memory)
    (hs : ShaStartState W b s argc) {a0 : List Byte} {names : List (List Byte)}
    (hR : names.length ≤ E.maxAllocs ∧ 0x8048 * names.length ≤ E.maxHeap ∧ names.length ≤ E.maxOpen)
    (hA : ∀ t, W.atMain t → ∃ C fi sti a0p g ops, ops.map Prod.snd = names ∧
      MainLibF E W b lb C fi sti t a0p a0 ops g)
    {dat : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.Bytes}
    (hops : ∀ n ∈ names, OpOk E dat n) (hne : ∀ n ∈ names, n ≠ []) (posix : Bool)
    (stdin : Silmaril.Apps.Sha256sum.Stdin) :
    MustQ W (Ended (Silmaril.Apps.Sha256sum.sha256sum (filesWorldN a0 names posix E.fs stdin)).status fun w =>
      w = (Silmaril.Apps.Sha256sum.sha256sum (filesWorldN a0 names posix E.fs stdin)).stdout.map UInt8.toBitVec ∧
      (Silmaril.Apps.Sha256sum.sha256sum (filesWorldN a0 names posix E.fs stdin)).stderr = []) s := by
  have := sha_not_lazy hload
  subst this
  have hb := XO.wo.hb
  refine sha_reaches_mainA XO.wo (shaMem_of_loaded hk hc hl hload) hs ?_
  intro t hC hj ho ha hK hcnt hat
  obtain ⟨C, fi, sti, a0p, g, ops, rfl, L⟩ := hA t hat
  obtain ⟨-, hbss, hbssw⟩ := shaTailMem_of_loaded hk hc hl hload
  have hhr := shaHr_of_loaded hk hc hl hload
  have hrw0 := shaRw_of_loaded hload
  have hI : ∀ n, n < 0xa188 → ∀ j, j < 8 → n + j < 0xa188 → ShaImg b ((b + BitVec.ofNat 64 n).toNat + j) :=
    fun n hn j hj hnj => by rw [addr_toNat (by omega)]; exact ⟨by omega, by omega⟩
  rw [← filesWorld_names]
  refine sha_main_multi_spec I M hopA XO (C := C) (fi := fi) (sti := sti) (a0p := a0p) (g := g)
    ⟨hC.rip, Silmaril.Elf.Link.Dyn.Hello.abiEntry_of hC.al hC.ret, hC.room, ⟨hC.done, ha, ho, hj⟩,
      (shaMemAll_of_loaded hk hc hl hsr hsc hload).keep hb hK, fun j hj => ?_, L.lo, L.env, L.hC, L.pinC,
      L.pinK, L.optC, L.optK, L.optL, L.opt, L.lbB, L.imgVar, L.argsImg, L.argv, L.argv0, L.argv0k,
      L.a0s, L.a0k, L.a0nz, L.noSlash, L.guard, L.guardk,
      ⟨⟨[], hj⟩, by rw [hcnt.1]; simpa using hR.1, by rw [hcnt.2.1]; simpa using hR.2.1,
        by rw [hcnt.2.2]; simpa using hR.2.2⟩⟩
    ⟨hC.ret, hC.al, L.lo, (shaMainAll_of_loaded hk hc hl hload).keepW hb (imgW_img hK),
      by rw [loadN_keeps hK (fun j hj => hI 0xa040 (by decide) j (by omega) (by omega))]; exact hbss,
      (hK.permitted (fun j hj => hI 0xa040 (by decide) j (by omega) (by omega))).2 hbssw,
      by rw [loadN_keeps hK (fun j hj => hI 0xa160 (by decide) j (by omega) (by omega))]; exact hhr,
      L.guard, L.guardk, L.guardImg, L.imgVar, L.argsImg, L.optK, L.args, L.ne, L.argc, L.argcLim, L.avLim⟩
    (fun pn hpn => hops pn.2 (List.mem_map_of_mem hpn))
    (fun pn hpn => hne pn.2 (List.mem_map_of_mem hpn)) posix stdin
  have hj' : ShaImg b (b.toNat + 0xa160 + j) := ⟨by omega, by omega⟩
  rw [(hK _ hj').2, (hK _ hj').2]
  exact hrw0 j hj

end Silmaril.Elf.Link.Dyn.Sha256sum
