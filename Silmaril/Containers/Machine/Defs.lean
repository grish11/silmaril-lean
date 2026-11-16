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

**In a runtime.** `MachRuntime I P E` names the parameters of a runtime over a machine: the
loader, the machine and what the runtime adds; `MachRuntime.toRuntime` is the runtime model, and
`MachRuntime.withMachine` replaces the machine and nothing else. The construction is
compositional and exact: the runs of an image are the loader's refusal, or the machine's runs of
the loaded program transformed by what the runtime adds (`Thms.MachRuntime.beh_iff`).

**Clone policies.** What a run does at a task-creation request is a parameter of the run
semantics (`ClonePolicy`), not of the machine: `seqPolicy` ends the run in undefined behaviour
(the sequential reading, `MachineSem.runs`); `machinePolicy` makes the request an internal step,
for a machine that implements threads in its own states and steps. A parallel machine needs its
own policy **and** a machine that implements task creation; changing only the machine's states
while keeping `seqPolicy` keeps thread creation undefined, and choosing `machinePolicy` for a
machine without threads makes thread creation a step that creates nothing.

**Runs** (`MachineSem.Run pol`), from an initial state and a finite execution of `ev` and `tau`
steps with events `t`:

* a final state with a stop: `done t s`;
* a task-creation request the policy rejects (`pol r = some u`): `done t (undefined u)`; under
  `seqPolicy` this is `threadCreate` for a thread or a task sharing the address space and
  `unmodeled` for a new process (`CloneReq.kind`); a request the policy accepts is an internal
  step;
* a state with no step and no final outcome: `done t (undefined stuck)`;
* a state whose only steps are inputs, which the environment may withhold: `blocked t`;
* an infinite execution of internal steps (`tau`, and accepted task creations): `spins t`;
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

/-- **A clone policy**: what a run does at a task-creation step. `some u`: the run ends in the
undefined behaviour `u`. `none`: the step is an internal step of the machine, which must then
*implement* task creation in its states and steps (a parallel machine with threads in its
state); choosing `none` for a machine that does not is unsound, because the request becomes a
step that creates nothing (`Silmaril.Containers.Mini.noTasks_threadSpawn_exits`). -/
abbrev ClonePolicy : Type := CloneReq → Option UB

/-- **The sequential policy**: every task-creation request ends the run in undefined behaviour
(`CloneReq.ub`: `threadCreate`, or `unmodeled` for a process). -/
def seqPolicy : ClonePolicy := fun r => some r.ub

/-- **The machine's own policy**: task creation is a step of the machine (for a machine whose
state has threads and a scheduler). -/
def machinePolicy : ClonePolicy := fun _ => none

/-- The internal actions under a policy: `tau`, and the task-creation requests the policy hands
to the machine. -/
def Internal {E : Type} (pol : ClonePolicy) : Act E → Prop
  | .tau => True
  | .clone r => pol r = none
  | .ev _ => False

namespace MachineSem

variable {P E : Type} (M : MachineSem P E)

/-- **Finite executions** of event and internal steps under a clone policy, with their events. -/
inductive Exec (pol : ClonePolicy) : M.State → List E → M.State → Prop where
  | refl (s : M.State) : Exec pol s [] s
  | internal {s s' s'' : M.State} {a : Act E} {t : List E} :
      Internal pol a → M.step s a s' → Exec pol s' t s'' → Exec pol s t s''
  | ev {s s' s'' : M.State} {e : E} {t : List E} :
      M.step s (.ev e) s' → Exec pol s' t s'' → Exec pol s (e :: t) s''

/-- **A stuck state**: no step and no final outcome. -/
def Stuck (s : M.State) : Prop := (∀ a s', ¬ M.step s a s') ∧ ∀ st, ¬ M.final s st

/-- **A waiting state**: not final, some input step is possible, and every step is an input. -/
def Waiting (s : M.State) : Prop :=
  (∀ st, ¬ M.final s st) ∧ (∃ e s', M.isIn e = true ∧ M.step s (.ev e) s') ∧
    ∀ a s', M.step s a s' → ∃ e, a = .ev e ∧ M.isIn e = true

/-- **Silent divergence** under a policy: an infinite sequence of internal steps. -/
def SilentDiv (pol : ClonePolicy) (s : M.State) : Prop :=
  ∃ f : Nat → M.State, f 0 = s ∧ ∀ n, ∃ a, Internal pol a ∧ M.step (f n) a (f (n + 1))

/-- **The runs of a program under a clone policy.** -/
inductive Run (pol : ClonePolicy) (p : P) : Beh E → Prop where
  | final {s s' : M.State} {t : List E} {st : Stop} :
      M.load p s → M.Exec pol s t s' → M.final s' st → Run pol p (.done t st)
  | clone {s s' s'' : M.State} {t : List E} {r : CloneReq} {u : UB} :
      M.load p s → M.Exec pol s t s' → M.step s' (.clone r) s'' → pol r = some u →
        Run pol p (.done t (.undefined u))
  | stuck {s s' : M.State} {t : List E} :
      M.load p s → M.Exec pol s t s' → M.Stuck s' → Run pol p (.done t (.undefined .stuck))
  | blocked {s s' : M.State} {t : List E} :
      M.load p s → M.Exec pol s t s' → M.Waiting s' → Run pol p (.blocked t)
  | spins {s s' : M.State} {t : List E} :
      M.load p s → M.Exec pol s t s' → M.SilentDiv pol s' → Run pol p (.spins t)
  | reactive (f : Nat → E) :
      (∀ n, ∃ s s', M.load p s ∧ M.Exec pol s ((List.range n).map f) s') →
        Run pol p (.reactive f)
  | noInit : (∀ s, ¬ M.load p s) → Run pol p (.done [] (.undefined .noInit))

/-- **The process semantics of a machine under a clone policy.** -/
def runsWith (pol : ClonePolicy) : ProcSem P E := M.Run pol

/-- **The sequential process semantics**: thread creation is undefined behaviour
(`seqPolicy`). This is a choice of policy, not a property of the machine. -/
def runs : ProcSem P E := M.runsWith seqPolicy

/-- **Explicit task creation** (an obligation of an instance): a step creates a task only as a
`clone` action. Stated over a predicate `creates` saying which steps of the instance create a
task. -/
def ClonesExplicit (creates : M.State → Act E → M.State → Prop) : Prop :=
  ∀ s a s', M.step s a s' → creates s a s' → ∃ r, a = .clone r

end MachineSem

/-- **A runtime model over a named machine.** The three parameters a runtime is built from: the
loader (images to programs), the machine (its memory, concurrency and scheduling model inside
its states and steps), and what the runtime adds to the machine's runs. -/
structure MachRuntime (I P E : Type) where
  load : I → Except Refusal P
  machine : MachineSem P E
  /-- What a run does at a task-creation request (`seqPolicy` for a sequential machine). -/
  policy : ClonePolicy := seqPolicy
  obs : Beh E → Beh E → Prop := Eq

/-- **The runtime model of a machine runtime**: `beh i b` exactly when the loader gives `p`, the
machine has the run `b₀` of `p` under the runtime's clone policy (`MachineSem.Run`), and the
runtime turns `b₀` into `b`; or the loader refuses (`Thms.MachRuntime.beh_iff`). -/
def MachRuntime.toRuntime {I P E : Type} (R : MachRuntime I P E) : Runtime I P E :=
  ⟨R.load, R.machine.runsWith R.policy, R.obs⟩

/-- **The same runtime over another machine and clone policy** (for example a parallel machine
with `machinePolicy` in place of a sequential one with `seqPolicy`): the loader and what the
runtime adds are kept. Changing the machine but keeping `seqPolicy` keeps thread creation
undefined, whatever the new machine's states can represent. -/
def MachRuntime.withMachine {I P E : Type} (R : MachRuntime I P E) (M : MachineSem P E)
    (pol : ClonePolicy) : MachRuntime I P E :=
  { R with machine := M, policy := pol }

/-- **A runtime model over a machine**: a loader to programs, and the machine's runs. -/
def _root_.Silmaril.Containers.Runtime.ofMachine {I P E : Type} (load : I → Except Refusal P)
    (M : MachineSem P E) (obs : Beh E → Beh E → Prop := Eq) : Runtime I P E :=
  ({ load, machine := M, obs } : MachRuntime I P E).toRuntime

/-- **Sequential agreement** (the transfer obligation from a sequential machine to another,
for example a parallel one): on the image `i`, every run under `Rpar` is a run under `Rseq`. -/
def SeqAgrees {I P P' E : Type} (Rpar : Runtime I P' E) (Rseq : Runtime I P E) (i : I) : Prop :=
  ∀ b, Rpar.beh i b → Rseq.beh i b

end Silmaril.Containers.Mach
