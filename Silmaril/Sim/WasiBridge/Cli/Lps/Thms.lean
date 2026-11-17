module

public import Silmaril.Sim.WasiBridge.Cli.Lps.Defs
public import Silmaril.Sim.WasiBridge.Cli.Sha256sum.Thms
public import Silmaril.Elf.LpsCli.Sha256sum.Thms
import Silmaril.Proofs.Sim.WasiBridge.Cli.Lps

/-!
# Static executables under LPS in the ELF ≡ WASI bridge

PROVED (standard axioms):

* `out1_obsTrace`: the bridge's `L1` observation of an LPS trace is `LpsCli.out1Of`;
* **`lpsModel_eq`**: `LpsCli.lpsModel file isa = traceModel (lpsTraces file isa)`;
* **`wasiSha256_of_static`**: a WASI preview1 program whose traces are `ElfWasiEquiv` to those of
  `sha256sum-min` under LPS (stdin by stdin) meets `Std.sha256Stdin`, i.e. it discharges
  `Task.wasiSha256`;
* `wasi_agrees_glibc_of_static`: such a WASI program agrees run by run with the real GNU
  `sha256sum` on glibc (and, by `static_agrees_glibc`, with `sha256sum-min`).

So the chain WASI ≡ static ELF (stated, `ElfWasiEquiv`) ⊨ `Std.sha256Stdin` (proved) ⫤ glibc
(proved) relates all three builds through one sentence. The converse direction (a proved WASI
`sha256sum` gives the static one) is `sha256_of_wasi` with `P := lpsTraces …`; it is redundant
for `sha256sum-min`, whose own proof is unconditional.
-/

@[expose] public section

namespace Silmaril.Sim.WasiBridge.Lps

open Silmaril.Process.LPS (Event)
open Silmaril.Cli.Institution (Level Model Sen Out1)
open Silmaril.Elf.LpsCli


theorem obsTrace_eq (tr : List Event) : obsTrace tr = (tr.filter Visible).map obs1 :=
  Silmaril.Proofs.Sim.WasiBridge.Cli.Lps.obsTrace_eq tr

theorem writtenOn_obsTrace (tr : List Event) : writtenOn 1 (obsTrace tr) = stdoutOf tr :=
  Silmaril.Proofs.Sim.WasiBridge.Cli.Lps.writtenOn_obsTrace tr

theorem endCode_obsTrace (tr : List Event) :
    endCode (obsTrace tr) = (exitOf tr).map (·.toNat) :=
  Silmaril.Proofs.Sim.WasiBridge.Cli.Lps.endCode_obsTrace tr

/-- **The bridge's observation of an LPS trace is `LpsCli.out1Of`.** -/
theorem out1_obsTrace (tr : List Event) : out1 (obsTrace tr) = out1Of tr :=
  Silmaril.Proofs.Sim.WasiBridge.Cli.Lps.out1_obsTrace tr

/-- **`lpsModel` is a trace model.** -/
theorem lpsModel_eq (file : Silmaril.Formats.ELF.Bytes) (isa : Isa) :
    lpsModel file isa = traceModel (lpsTraces file isa) :=
  Silmaril.Proofs.Sim.WasiBridge.Cli.Lps.lpsModel_eq file isa

theorem staticTraces_sat : (traceModel staticTraces).Sat Silmaril.Cli.Institution.Std.sha256Stdin :=
  Silmaril.Proofs.Sim.WasiBridge.Cli.Lps.staticTraces_sat

/-- **A WASI program equivalent to `sha256sum-min` discharges `Task.wasiSha256`.** -/
theorem wasiSha256_of_static {W : Silmaril.Cli.Bytes → P1Sem} {S : Subset}
    (hE : ∀ s, ElfWasiEquiv (staticTraces s) (W s) S) : Task.wasiSha256 W S :=
  Silmaril.Proofs.Sim.WasiBridge.Cli.Lps.wasiSha256_of_static hE

/-- **Such a WASI program agrees with GNU `sha256sum` on glibc.** -/
theorem wasi_agrees_glibc_of_static {W : Silmaril.Cli.Bytes → P1Sem} {S : Subset}
    (hE : ∀ s, ElfWasiEquiv (staticTraces s) (W s) S) {s : Silmaril.Cli.Bytes} {o o' : Out1}
    (h : (p1Model W S).Run s o) (h' : Silmaril.Elf.Link.Dyn.Sha256sum.stdinModel.Run s o') :
    o = o' :=
  Silmaril.Proofs.Sim.WasiBridge.Cli.Lps.wasi_agrees_glibc_of_static hE h h'

end Silmaril.Sim.WasiBridge.Lps
