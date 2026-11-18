module

public import Silmaril.Sim.WasiBridge.Cli.Defs

/-!
# Translation validation of CLI binaries: observable transition systems (definitions)

Translation validation (TV) proves one program equivalent to another by a **certificate**
checked per step (or per block), instead of proving either correct directly. Here the
programs are CLI processes compared by their observable traces (`Silmaril.Sim.WasiBridge.Obs`:
bytes read and written per descriptor, the exit status), so that a certificate transfers CLI
sentences (`Silmaril.Cli.Institution`) between an x86 binary, the same binary inside a Wasm
simulator, a sliced (smaller) simulator, and a WASI reference program. Design and survey:
`docs/cli-tv.md`.

**Signatures.**
* `Lts`: an observable transition system: a state type, an initial state, and steps labelled by
  a *word* of observables (a user instruction emits `[]`, a syscall the bytes it moved). `Run`
  its finite runs, `traces` the words of runs from the initial state.
* `WSim A B`: a weak forward simulation (each `A` step is matched by a `B` run emitting the same
  word). `Cert A B`: simulations both ways, **the TV certificate**: its traces are equivalent
  (`Cert.equiv`).
* `Slice A B`: a functional certificate: an abstraction `abs` of the states of `A` satisfying an
  invariant onto the states of a smaller system `B` (**the sliced simulator**: only the state and
  instructions the binary uses), forward and backward. `Slice.cert`.
* `procLts step E m e`: an x86 process under a syscall environment as an `Lts`; its traces are
  `procObs` (`procLts_traces`). `restrictStep Ok step`: the user step restricted to the states
  `Ok` accepts (**an instruction slice**: a simulator that models only the instruction forms
  `Ok` names and stops elsewhere).
* `Ended P`: the ended traces of `P` (last observable an exit), the only ones a CLI observation
  reads (`traceModel`); `EndedEquiv`, `ElfWasiEnded`: equivalence on ended traces, weaker than
  `ElfWasiEquiv` and insensitive to how a run splits its output into syscalls.

**The hello prototype.** `writeLoop fd msg code`: the sliced simulator of a write loop (its only
state is the bytes left to write): any number of bytes of `msg` per step on `fd`, then
`exit code`. `Task.helloLoopEnds`: some run of a proved x86 `hello` runtime ends (progress).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Sim.WasiBridge.Tv

open Silmaril.Machine.Process.LpsBridge
open Silmaril.Machine.Process.IoSpec
open Silmaril.X86 (MState)
open Silmaril.Process.LPS.Machines

/-! ## Observable transition systems -/

/-- **An observable transition system**: steps emit words of observables. -/
structure Lts where
  /-- States. -/
  St : Type
  /-- The initial state. -/
  init : St
  /-- Labelled steps. -/
  step : St → List Obs → St → Prop

/-- Finite runs, emitting the concatenation of their steps' words. -/
inductive Lts.Run (A : Lts) : A.St → List Obs → A.St → Prop
  | refl (s : A.St) : A.Run s [] s
  | cons {s s' s'' : A.St} {w t : List Obs} : A.step s w s' → A.Run s' t s'' →
      A.Run s (w ++ t) s''

/-- The observable traces: words of runs from the initial state. -/
def Lts.traces (A : Lts) : List Obs → Prop := fun t => ∃ s, A.Run A.init t s

/-! ## Certificates -/

/-- **A weak forward simulation** of `A` by `B`: related states, every `A` step matched by a
`B` run with the same word. -/
structure WSim (A B : Lts) where
  /-- The coupling relation. -/
  R : A.St → B.St → Prop
  /-- The initial states are coupled. -/
  init : R A.init B.init
  /-- Steps are matched. -/
  step : ∀ {s t w s'}, R s t → A.step s w s' → ∃ t', B.Run t w t' ∧ R s' t'

/-- **A translation-validation certificate**: simulations both ways. -/
structure Cert (A B : Lts) where
  /-- `A` simulated by `B`. -/
  fwd : WSim A B
  /-- `B` simulated by `A`. -/
  bwd : WSim B A

/-- **A slice**: `B` is an abstraction of `A` on the states of an invariant. `abs` forgets the
state `A`'s runs do not depend on (registers, memory and instructions the binary never uses,
or constant ones); `fwd` says every `A` step is an abstract run, `bwd` that every abstract step
is realised. -/
structure Slice (A B : Lts) where
  /-- The abstraction. -/
  abs : A.St → B.St
  /-- The invariant of `A`'s reachable states. -/
  Inv : A.St → Prop
  init_inv : Inv A.init
  init_abs : abs A.init = B.init
  fwd : ∀ {s w s'}, Inv s → A.step s w s' → Inv s' ∧ B.Run (abs s) w (abs s')
  bwd : ∀ {s w b'}, Inv s → B.step (abs s) w b' → ∃ s', A.Run s w s' ∧ Inv s' ∧ abs s' = b'

/-! ## Ended traces -/

/-- The ended traces of a trace set (the last observable is an exit). -/
def Ended (P : List Obs → Prop) : List Obs → Prop := fun t => P t ∧ (endCode t).isSome

/-- Equivalence on ended traces. -/
def EndedEquiv (P Q : List Obs → Prop) : Prop := Equiv (Ended P) (Ended Q)

/-- **ELF ≡ WASI on ended traces**: the process `P` and the WASI program `W` (within the
syscall subset `S`) have the same complete runs. Implied by `ElfWasiEquiv`
(`ElfWasiEquiv.ended`), and enough for every CLI sentence (`sat_iff_of_elfWasiEnded`). -/
def ElfWasiEnded (P : List Obs → Prop) (W : P1Sem) (S : Subset) : Prop :=
  EndedEquiv P (W.obs S)

/-! ## Processes as transition systems -/

/-- The steps of a process: user steps (silent), answered syscalls (their observables), and a
halting answer (to the dead state `none`). -/
inductive ProcStep (step : MState → Option MState) (E : SysEnv) :
    Option (MState × E.Model) → List Obs → Option (MState × E.Model) → Prop
  | user {m m' : MState} {e : E.Model} : step m = some m' → ProcStep step E (some (m, e)) [] (some (m', e))
  | resume {m m' : MState} {e e' : E.Model} {ch : X86FlagChoices.Choice} {evs : List Silmaril.Process.LPS.Event} :
      AtSyscall m → E.arm (trapped ⟨m, none⟩ ch) e (.resume m' e' evs) →
      ProcStep step E (some (m, e)) (obsTrace evs) (some (m', e'))
  | halt {m : MState} {e : E.Model} {ch : X86FlagChoices.Choice} {evs : List Silmaril.Process.LPS.Event} :
      AtSyscall m → E.arm (trapped ⟨m, none⟩ ch) e (.halt evs) →
      ProcStep step E (some (m, e)) (obsTrace evs) none

/-- **An x86 process as an observable transition system.** -/
def procLts (step : MState → Option MState) (E : SysEnv) (m : MState) (e : E.Model) : Lts :=
  ⟨Option (MState × E.Model), some (m, e), ProcStep step E⟩

/-- **An instruction slice of a user step**: the step on the states `Ok` accepts (e.g. those
whose next instruction is one of the forms a sliced simulator models), stuck elsewhere. -/
def restrictStep (Ok : MState → Prop) [DecidablePred Ok] (step : MState → Option MState) :
    MState → Option MState :=
  fun m => if Ok m then step m else none

/-! ## The hello prototype -/

/-- The steps of a write loop: write any prefix of what is left on `fd`, or exit when nothing
is left. -/
inductive WriteStep (fd code : Nat) :
    Option (List (BitVec 8)) → List Obs → Option (List (BitVec 8)) → Prop
  | write (r : List (BitVec 8)) (k : Nat) :
      WriteStep fd code (some r) ((r.take k).map (.wr fd)) (some (r.drop k))
  | exit : WriteStep fd code (some []) [.exit code] none

/-- **The sliced simulator of a write loop**: its state is only the bytes left to write (`none`
once exited); every other register, the code and the memory are constant or dead. -/
def writeLoop (fd : Nat) (msg : List (BitVec 8)) (code : Nat) : Lts :=
  ⟨Option (List (BitVec 8)), some msg, WriteStep fd code⟩

/-- **Task (progress of the x86 `hello` runtime)**: some run of a proved x86 `hello` runtime
(`Silmaril.Wasi.Runtime.HelloLoop`) on descriptor `1` ends with an exit. With the proved inclusion
`helloLoop_refines` this gives ended-trace equivalence with the preview1 `hello`
(`helloLoop_ended`), a weaker target than `Task.helloEquiv` that suffices for every CLI
sentence. -/
def Task.helloLoopEnds : Prop :=
  ∀ (c : MState → Option MState) (segs : List Silmaril.Process.LPS.Segment)
    (e : Silmaril.Process.LPS.Model) (R : Silmaril.Wasi.Runtime.HelloLoop c segs 1 e),
    (∀ m, AtSyscall m → c m = none) →
    ∃ t, procObs c (lpsEnv segs) R.start e t ∧ (endCode t).isSome

/-- **Task (a slice of the x86 `hello` runtime)**: the write-loop simulator is a slice of the
runtime's process, for the runtime's kernel write sizes. The slice route to
`Task.helloLoopEnds` and beyond (`Slice.cert`): the abstract machine has three kinds of steps,
and a proof of the slice is one obligation per instruction of the loop. Stated for the
write-loop abstraction with every write size (`lpsEnv`'s write arm allows any short write of at
least one byte; a step of size `0` is matched by the empty run). For an environment with full
writes only, a variant of the abstraction with restricted sizes is the related model to add. -/
def Task.helloLoopSlice : Prop :=
  ∀ (c : MState → Option MState) (segs : List Silmaril.Process.LPS.Segment)
    (e : Silmaril.Process.LPS.Model) (R : Silmaril.Wasi.Runtime.HelloLoop c segs 1 e),
    (∀ m, AtSyscall m → c m = none) →
    Nonempty (Slice (procLts c (lpsEnv segs) R.start e) (writeLoop 1 [0x68, 0x69] 0))

end Silmaril.Sim.WasiBridge.Tv
