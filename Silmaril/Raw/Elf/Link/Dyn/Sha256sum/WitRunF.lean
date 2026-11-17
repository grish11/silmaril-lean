module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.WitRun
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.WitMainF

/-! # GNU `sha256sum` witness: an actual run (file tier, `sha256sum f`)

The file-tier counterpart of `WitRun`. The concrete process `s0 argsF` (`argv = ["sha256sum", "f"]`)
in the world `Wfl d`: the file system `fsD d` (`f` holds `d`, every other file is empty), every
import bound to its contract, the library entering `main` with the resource invariant `InvR` and,
from the state the start-up produces, with `MainLibF` (`ArF`).

* `progress_invF`: every state of `Inv` has an outcome (`main` is entered at `entMF`);
* `sha256sum_files_runs`: from the kernel's state a run reaches the end with status 0 and standard
  output `hex(SHA-256(d)) ++ "  f\n"`.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum.Wit

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access Region Permissions)
open Silmaril.X86.RelIsa (Res RunsInR)
open Silmaril.X86.Ext (loadN)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Streams
open Silmaril.Elf.Link.Dyn.Streams.Total
open Silmaril.Elf.Link.Dyn.Imports

/-- The file system: `f` holds `d`, every other file is empty. -/
def fsD (d : List Byte) : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult :=
  fun n => if n = toSpec f00 then .ok (toSpec d) else .ok []

theorem fsD_ok (d : List Byte) : ∀ p e, fsD d p ≠ .openErr e := by
  intro p e h; unfold fsD at h; split at h <;> cases h

/-- The entries the start-up produces on the file tier. -/
def CondF (t : PState) : Prop :=
  Keeps Wf.Kept (s0 argsF).m.memory t.m.memory ∧ t.m.core.fsBase = fs0 ∧
    t.m.core.read .rsi = sp0 + 8#64 ∧ t.m.core.read .rdi = 2#64

/-- The library's guarantee at `main` on the file tier. -/
def AfilesD (d : List Byte) (t : PState) : Prop :=
  ∃ C fi sti a0p g ops, ops.map Prod.snd = [f00] ∧ MainLibF (E0 (fsD d)) Wf b0 lb0 C fi sti t a0p a00 ops g

def ArF (d : List Byte) (t : PState) : Prop := InvR t ∧ (CondF t → AfilesD d t)

/-- The concrete file-tier world. -/
def Wfl (d : List Byte) : World := Wof (fsD d) (ArF d)

theorem argsAt_trG {fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult}
    {A : PState → Prop} {m : Memory} :
    ∀ {q : Word} {ops : List (Word × List Byte)}, ArgsAt Wf m q ops → ArgsAt (Wof fs A) m q ops
  | _, [], _ => trivial
  | _, (_, _) :: _, ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, h3, h4, argsAt_trG h5⟩

theorem mainLibF_trG {fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult}
    {A : PState → Prop} {C : Nat → Prop} {fi : Word} {sti : St} {t : PState} {a0p : Word}
    {a0 : List Byte} {ops : List (Word × List Byte)} {g : Word}
    (h : MainLibF (E0 fs) Wf b0 lb0 C fi sti t a0p a0 ops g) :
    MainLibF (E0 fs) (Wof fs A) b0 lb0 C fi sti t a0p a0 ops g :=
  ⟨h.lo, ⟨h.env.out, h.env.err, h.env.inp, ⟨h.env.vars.out, h.env.vars.err, h.env.vars.kept, h.env.vars.bound⟩,
    h.env.np, h.env.wr⟩, h.hC, h.pinC, h.pinK, h.optC, h.optK, h.optL, h.opt, h.lbB, h.imgVar, h.argsImg,
    h.argv, h.argv0, h.argv0k, h.a0s, h.a0k, h.a0nz, h.noSlash, h.guard, h.guardk, h.guardImg,
    argsAt_trG h.args, h.ne, h.argc, h.argcLim, h.avLim⟩

theorem multiImpsG (fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult) (A : PState → Prop) :
    MultiImps (E0 fs) shaRep (Wof fs A) b0 lb0 kb0 sc0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
    slot_tailLaws (E0 fs) rfl (slot0 fs) out_ne0 (Wof fs A) (kept_arena fs A)
  exact ⟨digImps0 fs A, printImps0 fs A, h1, h2, h3, h4, h5, rfl, h6⟩

/-- `main` is entered: from the state the start-up produces with `MainLibF` (`entMF`), otherwise
on a fresh `mainMem`. -/
theorem main_totalF (d : List Byte) (s : PState) (f a1 a2 a3 : Word) (g : Ghost) :
    ∃ t, Enters (Wfl d) s t f ∧ t.m.core.read .rdi = a1 ∧ t.m.core.read .rsi = a2 ∧
      t.m.core.read .rdx = a3 ∧ t.g = g ∧ (Wfl d).atMain t := by
  by_cases hc : Keeps Wf.Kept (s0 argsF).m.memory s.m.memory ∧ s.m.core.fsBase = fs0 ∧ a1 = 2#64 ∧
      a2 = sp0 + 8#64
  · obtain ⟨hk, hfs, rfl, rfl⟩ := hc
    exact ⟨entMF f a3 g, enters_entMF s f a3 g hk hfs, coreMF_rdi f a3, coreMF_rsi f a3,
      coreMF_rdx f a3, rfl, invR_entMF f a3 g,
      fun _ => ⟨Cm (fsD d), inF, stdinSt [], sp0 + 64#64, guard0, [(sp0 + 74#64, f00)], rfl,
        mainLibF_entMF (fsD d) f a3 g⟩⟩
  · refine ⟨⟨⟨coreE f a1 a2 a3 s.m.core.fsBase, mainMem s.m.memory⟩, g⟩,
      enters_of (fun a => Iff.rfl) rfl s f a1 a2 a3 g _ _ (mainMem_kept (fun a => Iff.rfl) s.m.memory),
      coreE_rdi _ _ _ _ _, coreE_rsi _ _ _ _ _, coreE_rdx _ _ _ _ _, rfl, invR_mainMem s _ g, fun hC => ?_⟩
    exfalso
    obtain ⟨hk, hfs, hrsi, hrdi⟩ := hC
    exact hc ⟨hk.trans (Keeps.symm' (mainMem_kept (W := Wf) (fun a => Iff.rfl) s.m.memory)), hfs,
      by rw [← coreE_rdi f a1 a2 a3 s.m.core.fsBase]; exact hrdi,
      by rw [← coreE_rsi f a1 a2 a3 s.m.core.fsBase]; exact hrsi⟩

theorem progress_invF (d : List Byte) : ∀ s, Inv s → ∃ r, (proc (Wfl d)).step s r :=
  proc_progressP (Wfl d) Inv (by show b0.toNat + 0xa188 ≤ 2 ^ 62; rw [b0_toNat]; decide)
    (fun a h => by
      rcases h with h | h <;> simp only [Wfl, Wof, Wf, args0, tls0, sp0_toNat, fs0_toNat, lb0_toNat] at h <;> omega)
    (fun res slots h => by cases h)
    (fun n s hI => named_total (fsD d) (fsD_ok d) _ n s hI)
    (fun s f a1 a2 a3 g _ => main_totalF d s f a1 a2 a3 g)
    (fun s f g _ => call0_total (fsD d) _ s f g)
    (fun s g f st h => h)

theorem hargcF : ((stkOf argsF).drop 4096).take 8 =
    Silmaril.Machine.LittleEndian.encodeWords [BitVec.ofNat 64 argsF.length] := by
  rw [stkOf_af]; decide +kernel

theorem opOkD (d : List Byte) (hd : 64 + d.length ≤ S0) : OpOk (E0 (fsD d)) (fun _ => toSpec d) f00 :=
  ⟨by decide, by decide, by show fsD d (toSpec f00) = _; simp [fsD],
    by show (toSpec d).length ≤ S0 - 64; simp only [toSpec, List.length_map]; omega⟩

/-- `sha256sum_filesK` for the concrete world `Wfl d`. -/
theorem sha_files_must (d : List Byte) (hd : 64 + d.length ≤ S0) (posix : Bool)
    (stdin : Silmaril.Apps.Sha256sum.Stdin) :
    MustQ (Wfl d)
      (Ended (Silmaril.Apps.Sha256sum.sha256sum (filesWorldN a00 [f00] posix (E0 (fsD d)).fs stdin)).status fun w =>
        w = (Silmaril.Apps.Sha256sum.sha256sum (filesWorldN a00 [f00] posix (E0 (fsD d)).fs stdin)).stdout.map UInt8.toBitVec ∧
        (Silmaril.Apps.Sha256sum.sha256sum (filesWorldN a00 [f00] posix (E0 (fsD d)).fs stdin)).stderr = [])
      (s0 argsF) :=
  sha256sum_filesK hFk hFc hFl (rfl : ifn0 (lb0 + 0xb5210#64) = some sr0) (rfl : ifn0 (lb0 + 0xb4410#64) = some sc0)
    (mainImps0 (fsD d) _) (multiImpsG (fsD d) _) rfl (exitOk0 (fsD d) _) (loadedW _)
    (start0 (fsD d) _ argsF hargcF) (names := [f00])
    (by show 1 ≤ mAllocs ∧ 0x8048 * 1 ≤ mHeap ∧ 1 ≤ mOpen; decide)
    (fun t hat hk hfs hrsi hrdi => by
      obtain ⟨C, fi, sti, a0p, g, ops, hn, h⟩ := hat.2 ⟨hk, hfs, hrsi, by rw [hrdi]; decide⟩
      exact ⟨C, fi, sti, a0p, g, ops, hn, mainLibF_trG h⟩)
    (dat := fun _ => toSpec d) (by simp [opOkD d hd]) (by simp [f00]) posix stdin

/-- **GNU `sha256sum f` runs to completion** (file tier, against the specification).

For the concrete loaded process (`s0 argsF`: `sha256sum` loaded with `libcrypto.so.3`, `libc.so.6`
and `ld.so` holding the pinned chunks, `argv = ["sha256sum", "f"]`) in the concrete world `Wfl d`
(the file `f` holds `d`; every import bound to its contract, the slot stream representation,
resource bounds `mAllocs = 4` requests of `mHeap = 64 KiB`, `mOpen = 4` streams), a run exists
from the kernel's state and ends with the status and standard output of silmaril's
specification `Silmaril.Apps.Sha256sum.sha256sum` on `argv = ["sha256sum", "f"]`.

Model limit (not a property of `sha256sum`): the concrete stream representation holds a stream's
unread bytes in one 1 MiB slot, so `64 + d.length ≤ S0`.

Trusted base: as `sha256sum_stdin_runs_spec` (the x86 semantics `Silmaril.X86.Open9`, the process
model `Proc.proc`, the loader relation `ExeLoaded` and the pinned chunks, the import contracts of
`Streams.Defs`, `Imports.Defs` and `Proc.Defs`, the stream representation `slotRep` and the
concrete `Env`/`World` of `WitWorld`, silmaril's specification). -/
theorem sha256sum_files_runs_spec (d : List Byte) (hd : 64 + d.length ≤ S0) (posix : Bool)
    (stdin : Silmaril.Apps.Sha256sum.Stdin) :
    ∃ t, RunsInR (proc (Wfl d)) (fun _ => True) (s0 argsF) t ∧
      Ended (Silmaril.Apps.Sha256sum.sha256sum (filesWorldN a00 [f00] posix (E0 (fsD d)).fs stdin)).status (fun w =>
        w = (Silmaril.Apps.Sha256sum.sha256sum (filesWorldN a00 [f00] posix (E0 (fsD d)).fs stdin)).stdout.map UInt8.toBitVec ∧
        (Silmaril.Apps.Sha256sum.sha256sum (filesWorldN a00 [f00] posix (E0 (fsD d)).fs stdin)).stderr = []) t :=
  must_run_of_inv Inv trivial (sha_files_must d hd posix stdin) (inv_s0 _) (progress_invF d)
    (fun _ _ hI hs h => inv_step (fsD d) (ArF d) (fun _ h => h.1) hI hs h)

/-- The specification on `sha256sum f`: status 0, the record of `f`, no diagnostic. -/
theorem spec_f (d : List Byte) (posix : Bool) (stdin : Silmaril.Apps.Sha256sum.Stdin) :
    Silmaril.Apps.Sha256sum.sha256sum (filesWorldN a00 [f00] posix (E0 (fsD d)).fs stdin) =
      ⟨FilesSpec.fileLines (fun _ => toSpec d) [toSpec f00], [], 0⟩ :=
  FilesSpec.sha256sum_multi _ (toSpec a00) [toSpec f00] rfl (by simp)
    (fun f hf => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      subst hf
      exact verbatim_of (by decide) (by decide) (by decide))
    (fun _ => toSpec d)
    (fun f hf => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      subst hf
      show fsD d (toSpec f00) = _
      simp [fsD]) rfl

/-- **GNU `sha256sum f`: a run ends with status 0 and standard output
`hex(SHA-256(d)) ++ "  f\n"`**, where `d` is the contents of `f`. Same model, limit and trusted
base as `sha256sum_files_runs_spec`. -/
theorem sha256sum_files_runs (d : List Byte) (hd : 64 + d.length ≤ S0) :
    ∃ t, RunsInR (proc (Wfl d)) (fun _ => True) (s0 argsF) t ∧
      Ended 0 (fun w => w = hexOf (sha256 d) ++ [0x20#8, 0x20#8] ++ f00 ++ [0x0a#8]) t := by
  obtain ⟨t, hr, hE⟩ := sha256sum_files_runs_spec d hd false (.bytes [])
  refine ⟨t, hr, ?_⟩
  rw [spec_f] at hE
  obtain ⟨w, hdone, hw, -⟩ := hE
  have hl : (FilesSpec.fileLines (fun _ => toSpec d) [toSpec f00]).map UInt8.toBitVec = fileLineM (toSpec d) f00 := by
    rw [fileLineM_spec]; simp [FilesSpec.fileLines, ofSpec]
  refine ⟨w, hdone, ?_⟩
  rw [hw, hl, fileLineM, ofSpec_toSpec]

end Silmaril.Elf.Link.Dyn.Sha256sum.Wit
