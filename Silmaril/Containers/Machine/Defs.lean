module

public import Silmaril.Containers.Runtime.Defs

/-!
# Machine semantics: the pluggable machine under a container runtime

A runtime model (`Silmaril.Containers.Runtime`) takes a process semantics, the runs of each
program. This module builds process semantics from a **machine semantics** (`MachineSem P E`):
states, the initial states of a program, labelled steps and final states. The machine is a
parameter: its state holds whatever memory model, register file, threads and scheduler the
machine has, so a sequential x86-64 machine, a Wasm store, or a parallel x86-64 machine with
explicit scheduling and a weak memory model are all instances. Nothing here fixes a sequential
executable semantics.

**Steps.** A step is labelled by an action (`Act E`): an event with the environment (`ev e`),
an internal step (`tau`), or a **task-creation request** (`clone r`). Task creation is a
separate action so that the policy for it is visible and replaceable: a parallel machine
handles it in its own steps; the sequential reading (`MachineSem.runs`) makes thread creation
undefined behaviour.

**Runs** (`MachineSem.Run`), from an initial state and a finite execution of `ev` and `tau`
steps with events `t`:

* a final state with a stop: `done t s`;
* a task-creation request: `done t (undefined (CloneReq.ub r))`: `threadCreate` for a thread or a
  task sharing the address space, `unmodeled` for a new process (`CloneReq.kind`);
* a state with no step and no final outcome: `done t (undefined stuck)`;
* a state whose only steps are inputs, which the environment may withhold: `blocked t`;
* an infinite execution of internal steps: `spins t`;
* infinitely many events, every finite prefix of which some execution produces: `reactive f`
  (the limit closure: it may include infinite runs no single execution has, which only makes
  preconditions stronger);
* a program with no initial state: `done [] (undefined noInit)`.

So **undefined behaviour never removes runs**: a stuck machine, a missing initial state and
thread creation all produce runs that end in `Stop.undefined`, and every verification
precondition (`Silmaril.Containers.vpre`) excludes them (`Thms.not_wlp_of_stuck`,
`Thms.not_wlp_of_clone`, `Thms.not_wlp_of_noInit`).

**Thread creation on Linux x86-64, exactly.** Tasks are created by the system calls `clone`
(56), `fork` (57), `vfork` (58) and `clone3` (435); `fork` behaves as `clone` with flags
`SIGCHLD`, `vfork` as `clone` with `CLONE_VM | CLONE_VFORK | SIGCHLD`, and `clone3` takes its
flags in the first field of `struct clone_args`. A request creates a **thread** when its flags
contain `CLONE_THREAD` (`0x10000`), a **task sharing the address space** when they contain
`CLONE_VM` (`0x100`) but not `CLONE_THREAD` (`vfork`, glibc's `posix_spawn`), and a **process**
otherwise (`fork`). The sequential policy makes the first two `UB.threadCreate` (concurrent
access to shared memory is outside a sequential machine) and the third `UB.unmodeled` (no
process semantics is given, so no claim is made). It classifies the *request*: a request the
kernel rejects (`CLONE_THREAD` without `CLONE_SIGHAND` and `CLONE_VM` gives `EINVAL`) is
classified all the same, which can only reject more programs.

That an instance maps these system calls, and only these, to `clone` actions is an obligation of
the instance (`ClonesExplicit` names it); no instance in this module models system calls, and
no coverage of concrete system calls is claimed.

**Towards a parallel machine.** A parallel x86-64 instance has explicit threads, a scheduler (a
source of nondeterminism to be quantified over, with fairness as an assumption), shared memory
under x86-TSO with atomic read-modify-write instructions and fences, and defines data races or
other memory-model violations as `UB.memory` where its semantics does. Results for the
sequential machine do not transfer to it automatically: transfer needs a refinement obligation
(`SeqAgrees`) relating the parallel machine's runs to the sequential ones on the programs
considered (`Thms.wlp_transfer`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Containers.Mach

open Silmaril.Containers

/-! ## Task creation -/

/-- `CLONE_VM`: the new task shares the address space. -/
def CLONE_VM : UInt64 := 0x100

/-- `CLONE_VFORK`: the caller is suspended until the child execs or exits. -/
def CLONE_VFORK : UInt64 := 0x4000

/-- `CLONE_THREAD`: the new task is a thread of the caller's thread group. -/
def CLONE_THREAD : UInt64 := 0x10000

/-- `SIGCHLD`, the exit signal `fork` uses. -/
def SIGCHLD : UInt64 := 17

/-- **A task-creation request**, as a Linux x86-64 program makes it. -/
inductive CloneReq where
  /-- `clone` (system call 56) with its flags argument. -/
  | clone (flags : UInt64)
  /-- `clone3` (system call 435) with the `flags` field of its `struct clone_args`. -/
  | clone3 (flags : UInt64)
  /-- `fork` (system call 57). -/
  | fork
  /-- `vfork` (system call 58). -/
  | vfork
  deriving DecidableEq, Repr

/-- The x86-64 system call number of a request. -/
def CloneReq.sysno : CloneReq → Nat
  | .clone _ => 56
  | .fork => 57
  | .vfork => 58
  | .clone3 _ => 435

/-- The flags a request amounts to. -/
def CloneReq.flags : CloneReq → UInt64
  | .clone f | .clone3 f => f
  | .fork => SIGCHLD
  | .vfork => CLONE_VM ||| CLONE_VFORK ||| SIGCHLD

/-- What a request creates. -/
inductive TaskKind where
  | thread
  | sharedVm
  | process
  deriving DecidableEq, Repr

/-- **The kind of task a request creates**, from its flags. -/
def CloneReq.kind (r : CloneReq) : TaskKind :=
  if r.flags &&& CLONE_THREAD != 0 then .thread
  else if r.flags &&& CLONE_VM != 0 then .sharedVm
  else .process

/-- **The sequential policy**: thread creation and shared address spaces are undefined behaviour;
process creation is outside the model. -/
def CloneReq.ub (r : CloneReq) : UB :=
  match r.kind with
  | .thread | .sharedVm => .threadCreate
  | .process => .unmodeled

/-! ## Machines -/

/-- **An action** of a machine step. -/
inductive Act (E : Type) where
  | ev (e : E)
  | tau
  | clone (r : CloneReq)

/-- **A machine semantics** for programs `P` with environment events `E`. -/
structure MachineSem (P E : Type) where
  /-- Machine states: memory, registers, threads, scheduler, as the machine has them. -/
  State : Type
  /-- The events whose payload the environment chooses. -/
  isIn : E → Bool
  /-- The initial states of a program (nondeterministic: layout randomisation, initial
  memory contents). -/
  load : P → State → Prop
  /-- Labelled steps. -/
  step : State → Act E → State → Prop
  /-- Final states and how the run stops there (including undefined behaviour the machine
  detects itself, such as `UB.memory`). -/
  final : State → Stop → Prop

namespace MachineSem

variable {P E : Type} (M : MachineSem P E)

/-- **Finite executions** of event and internal steps, with their events. -/
inductive Exec : M.State → List E → M.State → Prop where
  | refl (s : M.State) : Exec s [] s
  | tau {s s' s'' : M.State} {t : List E} : M.step s .tau s' → Exec s' t s'' → Exec s t s''
  | ev {s s' s'' : M.State} {e : E} {t : List E} :
      M.step s (.ev e) s' → Exec s' t s'' → Exec s (e :: t) s''

/-- **A stuck state**: no step and no final outcome. -/
def Stuck (s : M.State) : Prop := (∀ a s', ¬ M.step s a s') ∧ ∀ st, ¬ M.final s st

/-- **A waiting state**: not final, some input step is possible, and every step is an input. -/
def Waiting (s : M.State) : Prop :=
  (∀ st, ¬ M.final s st) ∧ (∃ e s', M.isIn e = true ∧ M.step s (.ev e) s') ∧
    ∀ a s', M.step s a s' → ∃ e, a = .ev e ∧ M.isIn e = true

/-- **Silent divergence**: an infinite sequence of internal steps. -/
def SilentDiv (s : M.State) : Prop := ∃ f : Nat → M.State, f 0 = s ∧ ∀ n, M.step (f n) .tau (f (n + 1))

/-- **The runs of a program** under the sequential reading of task creation. -/
inductive Run (p : P) : Beh E → Prop where
  | final {s s' : M.State} {t : List E} {st : Stop} :
      M.load p s → M.Exec s t s' → M.final s' st → Run p (.done t st)
  | clone {s s' s'' : M.State} {t : List E} {r : CloneReq} :
      M.load p s → M.Exec s t s' → M.step s' (.clone r) s'' →
        Run p (.done t (.undefined r.ub))
  | stuck {s s' : M.State} {t : List E} :
      M.load p s → M.Exec s t s' → M.Stuck s' → Run p (.done t (.undefined .stuck))
  | blocked {s s' : M.State} {t : List E} :
      M.load p s → M.Exec s t s' → M.Waiting s' → Run p (.blocked t)
  | spins {s s' : M.State} {t : List E} :
      M.load p s → M.Exec s t s' → M.SilentDiv s' → Run p (.spins t)
  | reactive (f : Nat → E) :
      (∀ n, ∃ s s', M.load p s ∧ M.Exec s ((List.range n).map f) s') → Run p (.reactive f)
  | noInit : (∀ s, ¬ M.load p s) → Run p (.done [] (.undefined .noInit))

/-- **The process semantics of a machine.** -/
def runs : ProcSem P E := M.Run

/-- **Explicit task creation** (an obligation of an instance): a step creates a task only as a
`clone` action. Stated over a predicate `creates` saying which steps of the instance create a
task. -/
def ClonesExplicit (creates : M.State → Act E → M.State → Prop) : Prop :=
  ∀ s a s', M.step s a s' → creates s a s' → ∃ r, a = .clone r

end MachineSem

/-- **A runtime model over a machine**: a loader to programs, and the machine's runs. -/
def _root_.Silmaril.Containers.Runtime.ofMachine {I P E : Type} (load : I → Except Refusal P)
    (M : MachineSem P E) (obs : Beh E → Beh E → Prop := Eq) : Runtime I P E :=
  ⟨load, M.runs, obs⟩

/-- **Sequential agreement** (the transfer obligation from a sequential machine to another,
for example a parallel one): on the image `i`, every run under `Rpar` is a run under `Rseq`. -/
def SeqAgrees {I P P' E : Type} (Rpar : Runtime I P' E) (Rseq : Runtime I P E) (i : I) : Prop :=
  ∀ b, Rpar.beh i b → Rseq.beh i b

end Silmaril.Containers.Mach
