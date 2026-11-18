module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.WitNonVac

/-! # GNU `sha256sum` witness: what remains for a run (open goals)

`WitNonVac` shows the hypotheses of the loader-level theorems are jointly satisfiable. With every
reachable state of the concrete process having an outcome (local progress), a run ending as the
specification says follows (`stdin_run_of_reach`, `files_run_of_reach`, proved).

`Task.mainLibReach` (the library guarantee `Astdin` can be met when entering `main` from any gate
state with the kernel's kept memory and `fsBase`) is **proved** in `WitMain.task_mainLibReach`.
Progress is proved for the worlds of `WitRun`/`WitRunF` (`progress_inv`, `progress_invF`: every
state of the resource invariant has an outcome, since `malloc`/`fopen` are total contracts), which
give the runs `sha256sum_stdin_runs` and `sha256sum_files_runs`.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum.Wit

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.RelIsa (Res RunsInR)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Streams

/-- `main` can be entered with `Astdin` from every gate state the start-up can produce. -/
def Task.mainLibReach (fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult)
    (data : List Byte) : Prop :=
  64 + data.length ≤ Streams.Total.S0 →
  ∀ (u : PState) (f a3 : Word) (g : Ghost), u.m.core.rip = gate0 →
    Keeps Wf.Kept (s0 [a00]).m.memory u.m.memory → u.m.core.fsBase = fs0 →
    ∃ t, Enters Wf u t f ∧ t.m.core.read .rdi = 1#64 ∧ t.m.core.read .rsi = sp0 + 8#64 ∧
      t.m.core.read .rdx = a3 ∧ t.g = g ∧ Astdin fs data t

/-- **A run of the concrete stdin-tier process, from local progress**: if every state reachable
from `s0 [a00]` has an outcome, a run ends with the specification's status and output. -/
theorem stdin_run_of_reach (fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult)
    (data : List Byte) (posix : Bool) (fs' : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult)
    (hp : ∀ t, Reach (proc (Wof fs (Astdin fs data))) (s0 [a00]) t → ∃ r, (proc (Wof fs (Astdin fs data))).step t r) :
    ∃ t, RunsInR (proc (Wof fs (Astdin fs data))) (fun _ => True) (s0 [a00]) t ∧
      Ended (Silmaril.Apps.Sha256sum.sha256sum (stdinWorld a00 data posix fs')).status (fun w =>
        w = (Silmaril.Apps.Sha256sum.sha256sum (stdinWorld a00 data posix fs')).stdout.map UInt8.toBitVec ∧
        (Silmaril.Apps.Sha256sum.sha256sum (stdinWorld a00 data posix fs')).stderr = []) t :=
  must_run_of_reach trivial (sha_stdin_s0 fs data posix fs') hp

/-- The same for the file tier (`sha256sum f`). -/
theorem files_run_of_reach (posix : Bool) (stdin : Silmaril.Apps.Sha256sum.Stdin)
    (hp : ∀ t, Reach (proc (Wof fsE Afiles)) (s0 [a00, f00]) t → ∃ r, (proc (Wof fsE Afiles)).step t r) :
    ∃ t, RunsInR (proc (Wof fsE Afiles)) (fun _ => True) (s0 [a00, f00]) t ∧
      Ended (Silmaril.Apps.Sha256sum.sha256sum (filesWorldN a00 [f00] posix (E0 fsE).fs stdin)).status (fun w =>
        w = (Silmaril.Apps.Sha256sum.sha256sum (filesWorldN a00 [f00] posix (E0 fsE).fs stdin)).stdout.map UInt8.toBitVec ∧
        (Silmaril.Apps.Sha256sum.sha256sum (filesWorldN a00 [f00] posix (E0 fsE).fs stdin)).stderr = []) t :=
  must_run_of_reach trivial (sha_files_s0 posix stdin) hp

end Silmaril.Elf.Link.Dyn.Sha256sum.Wit
