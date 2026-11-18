module

public import Silmaril.Sim.WasiBridge.Defs
public import Silmaril.Apps.Sha256sum.Process

/-!
# System-call machines through the ELF ≡ WASI bridge (definitions)

silmaril's `Silmaril.Apps.Sha256sum.Sys` is a process model at the level of system calls: a
`Machine` issues `openat`/`read`/`write`/`close` calls, a kernel `Env` (`WorldStep w`, the
kernel of a world `w`) answers them, and `Exec M E s k evs n` is a run that ends in
`exit_group(n)` with the call/reply events `evs`. The reference program of `sha256sum`'s stdin
path (`Sys.refMachine`) and the x86 process model of the binary `sha256sum-min`
(`Sys.x86Machine`, `Sys.Init`) are machines of this model. This file reads such machines
through the bridge in two ways, per standard input `s` (the world `w s`):

* **as observable traces** (`machObs`): the prefixes of the observables (`Obs`) of exiting runs,
  `runObs evs n = evs.flatMap sevObs ++ [.exit n]`;
* **as a WASI preview1 program** (`machP1`): the prefixes of the lifted preview1 events of
  exiting runs, `runP1`: each call is replaced by the preview1 call the `sys2wasi` adapter makes
  (`sevP1`: `read ↦ fd_read`, `write ↦ fd_write`, `close ↦ fd_close`, exit `↦ proc_exit`),
  for the runs whose events the adapter represents (`SEvent.Repr`).

`Thms`: the two readings are `ElfWasiEquiv` (`machP1_equiv`), trace refinement of machines is
refinement of observable traces (`machObs_mono`), and a machine that `SatisfiesRel` the
`sha256sum` specification is a CLI model of it (`machModel_sat`).

**What the adapter covers.** `SEvent.Repr`: successful `read`, `write` and `close` with 32-bit
descriptors and counts. Not covered: `openat` (`path_open` needs a preopened directory and a
string path), error replies (Linux and preview1 number `errno`s differently: `EBADF` is 9 and
`errno::badf` 8), and calls that silmaril's model does not have (`fstat`, `fadvise64`, `brk`,
`mmap`; these are answered inside the simulator and have no observable). `sha256sum`'s stdin
path needs only the covered calls.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Sim.WasiBridge.Sys

open Silmaril.Wasi (WEv)
open Silmaril.Wasi.Versions.P1 (fn okAns)
open Silmaril.Apps.Sha256sum (Bytes World)
open Silmaril.Apps.Sha256sum.Sys (Machine Env Call Ret KState Exec)

/-- A call and its reply. -/
abbrev SEvent := Silmaril.Apps.Sha256sum.Sys.Event

/-- Bytes as the bridge's. -/
def bits (b : Bytes) : List (BitVec 8) := b.map UInt8.toBitVec

/-- **The events the adapter represents**: successful `read`, `write` and `close` whose
descriptors and counts fit preview1's 32-bit encoding. -/
def SEvent.Repr : SEvent → Prop
  | (.read fd n, .data _) => fd < 2 ^ 32 ∧ n < 2 ^ 32
  | (.write fd _, .ok k) => fd < 2 ^ 32 ∧ k < 2 ^ 32
  | (.close fd, .ok _) => fd < 2 ^ 32
  | _ => False

/-- The observables of an event: the bytes read, the bytes the kernel accepted. -/
def sevObs : SEvent → List Obs
  | (.read fd _, .data b) => (bits b).map (.rd fd)
  | (.write fd b, .ok k) => (bits (b.take k)).map (.wr fd)
  | _ => []

/-- **The adapter on an event**: the lifted preview1 call it makes. -/
def sevP1 : SEvent → List WEv
  | (.read fd n, .data b) => toP1 (.read fd n (bits b))
  | (.write fd b, .ok k) => toP1 (.write fd (bits b) k)
  | (.close fd, .ok _) => [.imp (fn "fd_close") [.u32 (BitVec.ofNat 32 fd)] (okAns none)]
  | _ => []

/-- The observables of an exiting run. -/
def runObs (evs : List SEvent) (n : Nat) : List Obs := evs.flatMap sevObs ++ [.exit n]

/-- The preview1 events of an exiting run. -/
def runP1 (evs : List SEvent) (n : Nat) : List WEv := evs.flatMap sevP1 ++ toP1 (.exit n)

variable (M : Machine) (env : World → Env) (init : World → M.State → Prop) (w : Bytes → World)

/-- **A machine as observable traces** (per standard input `s`, on the world `w s`): the
prefixes of the observables of its exiting runs from every initial state `init` admits. -/
def machObs (s : Bytes) : List Obs → Prop :=
  fun o => ∃ st evs n, init (w s) st ∧ Exec M (env (w s)) st (KState.init (w s)) evs n ∧
    o <+: runObs evs n

/-- **A machine as a WASI preview1 program** (per standard input `s`): the prefixes of the
adapter's images of its exiting runs whose events it represents. -/
def machP1 (s : Bytes) : P1Sem :=
  ⟨fun t => ∃ st evs n, init (w s) st ∧ Exec M (env (w s)) st (KState.init (w s)) evs n ∧
    (∀ e ∈ evs, SEvent.Repr e) ∧ t <+: runP1 evs n⟩

/-- Every exiting run on the worlds `w s` has only events the adapter represents. -/
def AllRepr : Prop :=
  ∀ s st evs n, init (w s) st → Exec M (env (w s)) st (KState.init (w s)) evs n →
    ∀ e ∈ evs, SEvent.Repr e

end Silmaril.Sim.WasiBridge.Sys
