module

-- variant-of: Task.wasiSha256 (sha256sum, stdin, L1) | style: WASI image of silmaril's reference program | see-also: Silmaril.Sim.WasiBridge.Cli.Sha256sum.Thms

public import Silmaril.Sim.WasiBridge.Cli.Sha256sumSys.Defs
public import Silmaril.Sim.WasiBridge.Sys.Thms
public import Silmaril.Sim.WasiBridge.Cli.Sha256sum.Thms
import Silmaril.Proofs.Sim.WasiBridge.Cli.Sha256sumSys

/-!
# sha256sum: WASI, simulator and native x86 builds, related (level `L1`)

PROVED (standard axioms):

* **`wasiSha256_ref`**: the WASI reference program `refP1` meets `Std.sha256Stdin`
  (`Task.wasiSha256 refP1 S1`), from silmaril's `Sys.ref_satisfies` through the adapter;
  `refObs_sat` for its observable traces; **`ref_equiv`**: the reference program is
  `ElfWasiEquiv` to its WASI reading (`ref_allRepr`: the adapter represents every exiting run);
* **`wasiSha256sum_sat`**: a WASI module that refines `refP1` (`Task.wasiRefinesRef`, e.g. the
  pinned `wasmFile`) meets the sentence;
* **`simSha256sum_sat`**, `sim_sat_of_refines`: an x86 build whose traces are `ElfWasiEquiv`
  to `refP1` (`Task.simSha256sumEquiv`; one inclusion suffices) meets the sentence;
  `simSha256sum_equiv_of_stack`: a layer stack gives the equivalence; **`stack_sat`**: then
  every layer of the stack meets it (the ELF in the WASM simulator included,
  `Stack.equiv_wasi`);
* **`native_sat_of_sim`**: with simulator soundness against a native process model
  (`Task.nativeInTraces M P`), the native binary (glibc or musl, a full CLI model `M`) meets the
  lifted sentence at the full level, and its `L1` reduct meets the sentence
  (`native_reduct_sat_of_sim`);
* **`sim_agrees_glibc`**: such a build agrees run by run with GNU `sha256sum` on glibc
  (`Dyn.Sha256sum.stdinModel`);
* `sha256sum-min`: **`min_sat`** (given silmaril's `Plan.S1Refines`), `min_refines_wasi`,
  **`min_equiv`** (with `Task.minComplete`: the binary is `ElfWasiEquiv` to `refP1`),
  `min_agrees_glibc`.

**Variants.** `Silmaril.Sim.WasiBridge.Cli.Sha256sum` states the same chain over an arbitrary WASI
program `W` and leaves `Task.wasiSha256 W S` open. This module fixes `W` to the reference
program's WASI image and proves the sentence for it, so the remaining tasks are trace
refinements (`Task.wasiRefinesRef`, `Task.simSha256sumEquiv`) that never mention SHA-256. Pro:
the specification is proved once, in silmaril, and every build reduces to a simulation. Con:
a build whose call pattern differs from the reference program (other read sizes, `fstat`,
`fadvise64`, no `close`) needs either a different reference program or only the observable
inclusion (`sim_sat_of_refines`), which is what the equivalence asks anyway.
-/

@[expose] public section

namespace Silmaril.Sim.WasiBridge.Sha256sumSys

open Silmaril.Sim.WasiBridge.Sys
open Silmaril.Apps.Sha256sum (Bytes World lit sha256sum)
open Silmaril.Apps.Sha256sum.Sys (refMachine refStep RefState WorldStep StdinDom Exec
  stdinRecord)
open Silmaril.Cli.Institution (Level Model Out1)
open Silmaril.Cli.Institution.Std (sha256Stdin)

/-! ## The reference program -/

theorem stdinWorld_dom (s : Bytes) : StdinDom (stdinWorld s) :=
  Silmaril.Proofs.Sim.WasiBridge.Cli.Sha256sumSys.stdinWorld_dom s

theorem sha256sum_stdinWorld (s : Bytes) :
    sha256sum (stdinWorld s) = { stdout := stdinRecord s, stderr := [], status := 0 } :=
  Silmaril.Proofs.Sim.WasiBridge.Cli.Sha256sumSys.sha256sum_stdinWorld s

theorem ref_satisfiesRel :
    Silmaril.Apps.Sha256sum.Sys.SatisfiesRel refMachine WorldStep refInit StdinDom :=
  Silmaril.Proofs.Sim.WasiBridge.Cli.Sha256sumSys.ref_satisfiesRel

/-- **The reference program's observable traces meet the standard sentence.** -/
theorem refObs_sat : (traceModel refObs).Sat sha256Stdin :=
  Silmaril.Proofs.Sim.WasiBridge.Cli.Sha256sumSys.refObs_sat

/-- **The WASI reference program meets the standard sentence.** -/
theorem wasiSha256_ref : Task.wasiSha256 refP1 S1 :=
  Silmaril.Proofs.Sim.WasiBridge.Cli.Sha256sumSys.wasiSha256_ref

/-- No exiting run starts from `failed`. -/
theorem not_exec_failed {E : Silmaril.Apps.Sha256sum.Sys.Env} {k : Silmaril.Apps.Sha256sum.Sys.KState}
    {evs : List SEvent} {n : Nat} : ¬ Exec refMachine E .failed k evs n :=
  Silmaril.Proofs.Sim.WasiBridge.Cli.Sha256sumSys.not_exec_failed

theorem ref_repr {w : World} {st : refMachine.State} {k : Silmaril.Apps.Sha256sum.Sys.KState}
    {evs : List SEvent} {n : Nat} (h : Exec refMachine (WorldStep w) st k evs n)
    (hi : RInv st) : ∀ e ∈ evs, SEvent.Repr e :=
  Silmaril.Proofs.Sim.WasiBridge.Cli.Sha256sumSys.ref_repr h hi

/-- **The adapter represents every exiting run of the reference program.** -/
theorem ref_allRepr : AllRepr refMachine WorldStep refInit stdinWorld :=
  Silmaril.Proofs.Sim.WasiBridge.Cli.Sha256sumSys.ref_allRepr

/-- **The reference program is `ElfWasiEquiv` to its WASI reading.** -/
theorem ref_equiv (s : Bytes) : ElfWasiEquiv (refObs s) (refP1 s) S1 :=
  Silmaril.Proofs.Sim.WasiBridge.Cli.Sha256sumSys.ref_equiv s

/-! ## A WASI module -/

/-- **A WASI sha256sum that refines the reference program meets the standard sentence.** -/
theorem wasiSha256sum_sat {W : Bytes → P1Sem} (h : Task.wasiRefinesRef W) :
    Task.wasiSha256 W S1 :=
  Silmaril.Proofs.Sim.WasiBridge.Cli.Sha256sumSys.wasiSha256sum_sat h

/-! ## x86 builds in the simulator -/

/-- An x86 build whose traces are among the WASI reference program's meets the sentence. -/
theorem sim_sat_of_refines {P : Bytes → List Obs → Prop}
    (h : ∀ s, Refines (P s) ((refP1 s).obs S1)) : (traceModel P).Sat sha256Stdin :=
  Silmaril.Proofs.Sim.WasiBridge.Cli.Sha256sumSys.sim_sat_of_refines h

/-- **An x86 build `ElfWasiEquiv` to the WASI sha256sum meets the standard sentence.** -/
theorem simSha256sum_sat {P : Bytes → List Obs → Prop} (h : Task.simSha256sumEquiv P) :
    (traceModel P).Sat sha256Stdin :=
  Silmaril.Proofs.Sim.WasiBridge.Cli.Sha256sumSys.simSha256sum_sat h

/-- A layer stack gives the equivalence. -/
theorem simSha256sum_equiv_of_stack {P : Bytes → List Obs → Prop} (h : Task.sha256Stack P) :
    Task.simSha256sumEquiv P :=
  Silmaril.Proofs.Sim.WasiBridge.Cli.Sha256sumSys.simSha256sum_equiv_of_stack h

/-- Every layer of a stack is equivalent to its WASI layer. -/
theorem Stack.equiv_wasi (K : Stack) : ∀ l, Equiv (K.obs l) (K.obs .wasi) :=
  Silmaril.Proofs.Sim.WasiBridge.Cli.Sha256sumSys.Stack.equiv_wasi K

/-- **Every layer of a sha256sum stack meets the standard sentence**: the ELF, the ELF run in
the WASM simulator (`.bytesSim`), the P-calls and L forms, the adapted module. -/
theorem stack_sat (K : Bytes → Stack) (hW : ∀ s, (K s).obs .wasi = (refP1 s).obs S1)
    (l : Layer) : (stackModel K l).Sat sha256Stdin :=
  Silmaril.Proofs.Sim.WasiBridge.Cli.Sha256sumSys.stack_sat K hW l

/-! ## Native binaries -/

/-- The native binary meets the lifted sentence, given its runs among traces that refine the
WASI sha256sum. -/
theorem native_sat_of_refines {M : Model Level.full.sig} {P : Bytes → List Obs → Prop}
    (h : ∀ s, Refines (P s) ((refP1 s).obs S1)) (hT : Task.nativeInTraces M P) :
    M.Sat (Level.lift sha256Stdin) :=
  Silmaril.Proofs.Sim.WasiBridge.Cli.Sha256sumSys.native_sat_of_refines h hT

/-- **From the simulator to the native binary**: an x86 build `ElfWasiEquiv` to the WASI
sha256sum in the simulator, with the native process model's runs among its traces (simulator
soundness, `Task.nativeInTraces`), makes the native binary (GNU `sha256sum` on glibc, a static
musl build: a full CLI model `M`) meet the lifted standard sentence. -/
theorem native_sat_of_sim {M : Model Level.full.sig} {P : Bytes → List Obs → Prop}
    (hE : Task.simSha256sumEquiv P) (hT : Task.nativeInTraces M P) :
    M.Sat (Level.lift sha256Stdin) :=
  Silmaril.Proofs.Sim.WasiBridge.Cli.Sha256sumSys.native_sat_of_sim hE hT

/-- The same at level `L1`. -/
theorem native_reduct_sat_of_sim {M : Model Level.full.sig} {P : Bytes → List Obs → Prop}
    (hE : Task.simSha256sumEquiv P) (hT : Task.nativeInTraces M P) :
    (Level.stream.reduct M).Sat sha256Stdin :=
  Silmaril.Proofs.Sim.WasiBridge.Cli.Sha256sumSys.native_reduct_sat_of_sim hE hT

/-- **A simulator build agrees with GNU `sha256sum` on glibc**, run by run. -/
theorem sim_agrees_glibc {P : Bytes → List Obs → Prop} (hE : Task.simSha256sumEquiv P)
    {s : Bytes} {o o' : Out1} (h : (traceModel P).Run s o)
    (h' : Silmaril.Elf.Link.Dyn.Sha256sum.stdinModel.Run s o') : o = o' :=
  Silmaril.Proofs.Sim.WasiBridge.Cli.Sha256sumSys.sim_agrees_glibc hE h h'

/-! ## `sha256sum-min` -/

theorem min_refines_ref (h : Silmaril.Apps.Sha256sum.Plan.S1Refines)
    (r11Of : Silmaril.X86.State → Silmaril.X86.Word) (s : Bytes) :
    Refines (minObs r11Of s) (refObs s) :=
  Silmaril.Proofs.Sim.WasiBridge.Cli.Sha256sumSys.min_refines_ref h r11Of s

/-- **`sha256sum-min` meets the standard sentence**, given silmaril's S1 refinement target. -/
theorem min_sat (h : Silmaril.Apps.Sha256sum.Plan.S1Refines)
    (r11Of : Silmaril.X86.State → Silmaril.X86.Word) :
    (traceModel (minObs r11Of)).Sat sha256Stdin :=
  Silmaril.Proofs.Sim.WasiBridge.Cli.Sha256sumSys.min_sat h r11Of

/-- Its traces are among the WASI reference program's. -/
theorem min_refines_wasi (h : Silmaril.Apps.Sha256sum.Plan.S1Refines)
    (r11Of : Silmaril.X86.State → Silmaril.X86.Word) (s : Bytes) :
    Refines (minObs r11Of s) ((refP1 s).obs S1) :=
  Silmaril.Proofs.Sim.WasiBridge.Cli.Sha256sumSys.min_refines_wasi h r11Of s

/-- **`sha256sum-min` ≡ the WASI sha256sum**, given S1 refinement and completeness. -/
theorem min_equiv (h : Silmaril.Apps.Sha256sum.Plan.S1Refines)
    (r11Of : Silmaril.X86.State → Silmaril.X86.Word) (hc : Task.minComplete r11Of) :
    Task.simSha256sumEquiv (minObs r11Of) :=
  Silmaril.Proofs.Sim.WasiBridge.Cli.Sha256sumSys.min_equiv h r11Of hc

/-- `sha256sum-min` agrees with GNU `sha256sum` on glibc, run by run. -/
theorem min_agrees_glibc (h : Silmaril.Apps.Sha256sum.Plan.S1Refines)
    (r11Of : Silmaril.X86.State → Silmaril.X86.Word) {s : Bytes} {o o' : Out1}
    (hr : (traceModel (minObs r11Of)).Run s o)
    (h' : Silmaril.Elf.Link.Dyn.Sha256sum.stdinModel.Run s o') : o = o' :=
  Silmaril.Proofs.Sim.WasiBridge.Cli.Sha256sumSys.min_agrees_glibc h r11Of hr h'

end Silmaril.Sim.WasiBridge.Sha256sumSys
