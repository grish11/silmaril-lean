module

public import Silmaril.Sim.WasiBridge.Cli.Thms
public import Silmaril.Cli.Institution.Std.Thms
public import Silmaril.Elf.Link.Dyn.Sha256sum.Cli.Thms

/-!
# sha256sum across native, simulated and WASI builds (level `L1`)

The standard sentence `Std.sha256Stdin` is the meeting point:

* **glibc** (proved): `Sha256sum.stdinModel_std`, the pinned GNU `sha256sum` on glibc;
* **WASI** (stated): `Task.wasiSha256 W S`, a preview1 `sha256sum` (per stdin, a `P1Sem`) within
  the syscall subset `S` meets it;
* **an x86 build in the simulator or under LPS** (e.g. a static musl `sha256sum`), as observable
  traces `P`: `ElfWasiEquiv (P s) (W s) S` for every stdin.

PROVED (standard axioms), conditional on the stated tasks where named:

* `sha256_of_wasi`: given `Task.wasiSha256 W S` and `ElfWasiEquiv`, the x86 traces meet the
  sentence;
* `sha256_agrees_glibc`: then every run of that x86 build agrees with every run of GNU
  `sha256sum` on glibc on the same stdin (equal stdout and exit code);
* `sha256_native_of_wasi`: given also `Task.nativeInTraces M P`, a full model `M` (the musl or
  glibc binary under its own process model) meets the lifted sentence.
-/

@[expose] public section

namespace Silmaril.Sim.WasiBridge

open Silmaril.Cli (Bytes)
open Silmaril.Cli.Institution (Level Model Sen Out1)
open Silmaril.Cli.Institution.Std (sha256Stdin)

/-- **Task (a WASI sha256sum)**: the preview1 program meets the standard sentence. -/
def Task.wasiSha256 (W : Bytes → P1Sem) (S : Subset) : Prop := (p1Model W S).Sat sha256Stdin

theorem sha256_of_wasi {P : Bytes → List Obs → Prop} {W : Bytes → P1Sem} {S : Subset}
    (hW : Task.wasiSha256 W S) (hE : ∀ s, ElfWasiEquiv (P s) (W s) S) :
    (traceModel P).Sat sha256Stdin :=
  (sat_iff_of_elfWasiEquiv hE _).mpr hW

/-- **A WASI-equivalent x86 build agrees with GNU `sha256sum` on glibc.** -/
theorem sha256_agrees_glibc {P : Bytes → List Obs → Prop} {W : Bytes → P1Sem} {S : Subset}
    (hW : Task.wasiSha256 W S) (hE : ∀ s, ElfWasiEquiv (P s) (W s) S) {s : Bytes} {o o' : Out1}
    (h : (traceModel P).Run s o)
    (h' : Silmaril.Elf.Link.Dyn.Sha256sum.stdinModel.Run s o') : o = o' :=
  Silmaril.Cli.Institution.Std.sha256Stdin_agree (sha256_of_wasi hW hE)
    Silmaril.Elf.Link.Dyn.Sha256sum.stdinModel_std h h'

theorem sha256_native_of_wasi {M : Model Level.full.sig} {P : Bytes → List Obs → Prop}
    {W : Bytes → P1Sem} {S : Subset} (hW : Task.wasiSha256 W S)
    (hE : ∀ s, ElfWasiEquiv (P s) (W s) S) (hT : Task.nativeInTraces M P) :
    M.Sat (Level.lift sha256Stdin) :=
  native_sat_of_wasi hW hE hT

end Silmaril.Sim.WasiBridge
