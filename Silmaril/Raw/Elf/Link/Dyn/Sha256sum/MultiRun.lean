module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MultiLoaded
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.StdinRun

/-! # GNU `sha256sum FILE1 … FILEn`: the weaker library hypothesis at `main`

`MultiLoaded.sha256sum_files` has the same form of `hA` as the stdin tier, and the same finding
applies (`StdinRun.sha_stdin_no_progress`: `MainLibF` fixes `argc`, `argv`, the guard). Here is the
weakened statement `sha256sum_filesK` (via `StdinRun.sha_reaches_mainK`); the original follows
(`sha256sum_files_of_K`).
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- `MultiLoaded.sha256sum_files` with the weaker library hypothesis of `StdinRun.sha256sum_stdinK`:
`hA` only at `main` entries with the kernel's kept memory, `fsBase`, `argv` and `argc`. -/
theorem sha256sum_filesK {Fk Fc Fl : Blob} (hk : ChunksOf Fk cryptoChunks) (hc : ChunksOf Fc libcChunks)
    (hl : ChunksOf Fl ldChunks) {b kb lb ldb res sr sc : Word} {ifn : Word → Option Word} {lazy : Bool}
    (hsr : ifn (lb + 0xb5210#64) = some sr) (hsc : ifn (lb + 0xb4410#64) = some sc)
    {E : Env} {R : ShaRep} {W : World} (I : MainImps E W b lb sr) (M : MultiImps E R W b lb kb sc)
    (hopA : E.optindA = lb + 0x204248#64) (XO : ExitOk E W b lb) {s : PState} {argc : Word}
    (hload : ExeLoaded [shaFile, Fk, Fc, Fl] [b, kb, lb, ldb] ifn lazy res s.m.memory)
    (hs : ShaStartState W b s argc) {a0 : List Byte} {names : List (List Byte)}
    (hR : names.length ≤ E.maxAllocs ∧ 0x8048 * names.length ≤ E.maxHeap ∧ names.length ≤ E.maxOpen)
    (hA : ∀ t, W.atMain t → Keeps W.Kept s.m.memory t.m.memory → t.m.core.fsBase = s.m.core.fsBase →
      t.m.core.read .rsi = s.m.core.read .rsp + 8#64 → t.m.core.read .rdi = (argc.setWidth 32).setWidth 64 →
      ∃ C fi sti a0p g ops, ops.map Prod.snd = names ∧ MainLibF E W b lb C fi sti t a0p a0 ops g)
    {dat : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.Bytes}
    (hops : ∀ n ∈ names, OpOk E dat n) (hne : ∀ n ∈ names, n ≠ []) (posix : Bool)
    (stdin : Silmaril.Apps.Sha256sum.Stdin) :
    MustQ W (Ended (Silmaril.Apps.Sha256sum.sha256sum (filesWorldN a0 names posix E.fs stdin)).status fun w =>
      w = (Silmaril.Apps.Sha256sum.sha256sum (filesWorldN a0 names posix E.fs stdin)).stdout.map UInt8.toBitVec ∧
      (Silmaril.Apps.Sha256sum.sha256sum (filesWorldN a0 names posix E.fs stdin)).stderr = []) s := by
  have := sha_not_lazy hload
  subst this
  have hb := XO.wo.hb
  refine sha_reaches_mainK XO.wo (shaMem_of_loaded hk hc hl hload) hs ?_
  intro t hC hj ho ha hKK hfs hrsi hrdi hcnt hat
  have hK : Keeps (ShaImg b) s.m.memory t.m.memory := skeepsImgW XO.wo.img hKK
  obtain ⟨C, fi, sti, a0p, g, ops, rfl, L⟩ := hA t hat hKK hfs hrsi hrdi
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

theorem sha256sum_files_of_K {Fk Fc Fl : Blob} (hk : ChunksOf Fk cryptoChunks) (hc : ChunksOf Fc libcChunks)
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
      (Silmaril.Apps.Sha256sum.sha256sum (filesWorldN a0 names posix E.fs stdin)).stderr = []) s :=
  sha256sum_filesK hk hc hl hsr hsc I M hopA XO hload hs hR (fun t h _ _ _ _ => hA t h) hops hne posix stdin

end Silmaril.Elf.Link.Dyn.Sha256sum
