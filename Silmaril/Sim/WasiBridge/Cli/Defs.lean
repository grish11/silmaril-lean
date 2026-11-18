module

public import Silmaril.Sim.WasiBridge.Defs
public import Silmaril.Cli.Institution.Defs

/-!
# Observable traces as models of the CLI institution

The ELF ≡ WASI bridge (`Silmaril.Sim.WasiBridge`) compares programs by their **observable traces**
(`List Obs`: bytes read from and written to descriptors, the exit status). An ended trace (its
last observable an exit) is a CLI observation: the bytes written to descriptor 1 (and 2), and
the status as an exit code (`out1`, `outCmd`).

* `traceModel P` (level `L1`): for each stdin `s`, the ended traces of `P s`; `traceModelCmd P`
  (level `L2`), for semantics indexed by the program name, arguments and stdin.
* The standard instances: `elfModel` (an x86 process under an LPS syscall environment,
  `procObs`), `p1Model` (a WASI preview1 program within a syscall subset, `P1Sem.obs`),
  `stackModel K l` (layer `l` of a family of layer stacks, e.g. `.bytesSim`: the ELF run inside
  the WASM simulator).

`Thms`: equivalent trace semantics are the same model (`traceModel_eq`), so **`ElfWasiEquiv`
transfers satisfaction both ways** (`sat_iff_of_elfWasiEquiv`), along a whole stack
(`stack_sat_iff`); and a native model whose runs are among the traces satisfies what the
WASI program satisfies (`native_sat_of_wasi`, conditional on that inclusion).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Sim.WasiBridge

open Silmaril.Cli (Bytes)
open Silmaril.Cli.Institution (Level Model Out1 In2)

/-- The bytes written to descriptor `fd`. -/
def writtenOn (fd : Nat) (o : List Obs) : List (BitVec 8) :=
  o.filterMap fun
    | .wr d b => if d = fd then some b else none
    | _ => none

/-- The bytes read from descriptor `fd`. -/
def readOn (fd : Nat) (o : List Obs) : List (BitVec 8) :=
  o.filterMap fun
    | .rd d b => if d = fd then some b else none
    | _ => none

/-- The exit status of an ended trace: its last observable is an exit. -/
def endCode (o : List Obs) : Option Nat :=
  match o.getLast? with
  | some (.exit c) => some c
  | _ => none

/-- Bytes as the CLI model's. -/
def cliBytes (b : List (BitVec 8)) : Bytes := b.map UInt8.ofBitVec

/-- **The `L1` observation of an ended trace.** -/
def out1 (o : List Obs) : Option Out1 :=
  (endCode o).map fun c => { stdout := cliBytes (writtenOn 1 o), exit := UInt8.ofNat c }

/-- **The `L2` observation of an ended trace.** -/
def outCmd (o : List Obs) : Option Silmaril.Cli.Spec.Out :=
  (endCode o).map fun c =>
    { stdout := cliBytes (writtenOn 1 o), stderr := cliBytes (writtenOn 2 o), exit := UInt8.ofNat c }

/-- **The CLI model of a trace semantics** (level `L1`): per stdin, its ended traces. -/
def traceModel (P : Bytes → List Obs → Prop) : Model Level.stream.sig :=
  ⟨fun s o => ∃ t, P s t ∧ out1 t = some o⟩

/-- The CLI model of a trace semantics indexed by the whole command (level `L2`). -/
def traceModelCmd (P : In2 → List Obs → Prop) : Model Level.command.sig :=
  ⟨fun i o => ∃ t, P i t ∧ outCmd t = some o⟩

/-- **An x86 process** under the LPS syscall environment the stdin selects. -/
def elfModel (step : Silmaril.X86.MState → Option Silmaril.X86.MState)
    (E : Bytes → Silmaril.Machine.Process.IoSpec.SysEnv) (m : Silmaril.X86.MState)
    (e : (s : Bytes) → (E s).Model) : Model Level.stream.sig :=
  traceModel fun s => procObs step (E s) m (e s)

/-- **A WASI preview1 program** (per stdin), within the syscall subset `S`. -/
def p1Model (W : Bytes → P1Sem) (S : Subset) : Model Level.stream.sig :=
  traceModel fun s => (W s).obs S

/-- **Layer `l` of a family of layer stacks** (per stdin): `.elf` the process, `.bytesSim` the
ELF run inside the WASM simulator, `.wasi` the WASI program. -/
def stackModel (K : Bytes → Stack) (l : Layer) : Model Level.stream.sig :=
  traceModel fun s => (K s).obs l

end Silmaril.Sim.WasiBridge
