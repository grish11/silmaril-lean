module

public import Silmaril.Containers.Env.Defs

/-!
# Behaviours of a containerised process, and what specifications say about them

**Behaviours.** One run of a process, as its environment sees it (`Beh E`, events `E`):

* `done t s`: the events `t`, then the process stopped (`Stop`): it exited with a status, was
  killed by a signal of its own making (`signaled`: a crash such as `SIGSEGV` or `abort`), was
  stopped by the runtime (`killed`: out of memory, a timeout, a policy violation), or was never
  started (`refused`: a missing blob, a bad digest, an image without the expected shape);
* `blocked t`: the events `t`, then it waits for an input the environment never supplies;
* `spins t`: the events `t`, then it runs forever without another event (silent divergence);
* `reactive f`: infinitely many events (a server that keeps serving).

`blocked` and `spins` are kept apart because they are told apart by different assumptions:
blocking ends when the environment supplies input (a liveness assumption on the environment),
spinning never does. A stop by the runtime (`killed`) is kept apart from the program's own crash
(`signaled`) because runtime models differ in which kills they allow
(`Silmaril.Containers.Runtime`).

**Models and specifications.** A model (`Model E`) is the set of behaviours of a program in all
environments: the environment's choices (inputs) and the program's own nondeterminism are both
in the set. A specification is a predicate on behaviours (`Spec E`), satisfied when every
behaviour satisfies it (`Model.Sat`).

* **Safety** (`Spec.safe S`): every finite prefix satisfies `S`. Safety is what finite tests can
  refute and what trace inclusion (`Model.TraceRefines`) preserves.
* **Partial correctness** (`Spec.partialCorrect post`): *if* the process exits, then `post`
  holds of its events and status. A process that crashes, spins or blocks satisfies it.
* **Total correctness** (`Spec.totalCorrect post`): the process exits, and `post` holds.
  Relative to an environment assumption (`Spec.under A φ`), for example "the environment
  eventually supplies every input it is waited on for" (`Beh.notBlocked`).
* **Fairness** for infinite behaviours is a property of the infinite sequence of events
  (`Beh.InfinitelyOften`); liveness under fairness is `Spec.under` with a fairness assumption.

**Refinement.** `Model.Refines M N` is inclusion of behaviours: it preserves every specification
(`Thms.Refines.sat`), divergence included. `Model.TraceRefines M N` is inclusion of finite
prefixes: it preserves safety only. A silently diverging process trace-refines one that exits
at once (`Thms.traceRefines_not_total`).

**Determinism.** `Model.DetUpToInputs isIn M`: two runs first differ only at an input event,
and runs with the same events stop the same way. Environmental nondeterminism (which octets
arrive) is allowed; internal nondeterminism (which of two outputs is produced) is not.

**Noninterference is relational.** `Model.Noninterference lowIn lowOut M` compares *pairs* of
runs: runs that agree on low inputs agree on low outputs. It is not a property of single
behaviours (`Thms.noninterference_not_trace_property`), so no trace property, such as memory
safety or the absence of arbitrary code execution, implies it
(`Thms.trace_property_not_noninterference`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Containers

/-- Why a runtime stopped a process. -/
inductive Kill where
  | oom
  | timeout
  | policy
  | external
  deriving DecidableEq, Repr

/-- Why a runtime refused to start an image. -/
inductive Refusal where
  | missingBlob
  | badDigest
  | noShape
  | resources
  | other
  deriving DecidableEq, Repr

/-- **How a run stopped.** -/
inductive Stop where
  /-- The process exited with this status. -/
  | exited (code : UInt8)
  /-- The process was killed by a signal it caused (a crash). -/
  | signaled (sig : Nat)
  /-- The runtime stopped the process. -/
  | killed (k : Kill)
  /-- The runtime never started the process. -/
  | refused (r : Refusal)
  deriving DecidableEq, Repr

/-- **One run** as the environment sees it. -/
inductive Beh (E : Type) where
  /-- Finitely many events, then a stop. -/
  | done (t : List E) (s : Stop)
  /-- Finitely many events, then waiting forever for an input that never comes. -/
  | blocked (t : List E)
  /-- Finitely many events, then running forever without events. -/
  | spins (t : List E)
  /-- Infinitely many events. -/
  | reactive (f : Nat → E)

namespace Beh

variable {E : Type}

/-- **`u` is a finite prefix of the events of `b`.** -/
def Prefix (b : Beh E) (u : List E) : Prop :=
  match b with
  | .done t _ | .blocked t | .spins t => u <+: t
  | .reactive f => u = (List.range u.length).map f

/-- The run stopped. -/
def Stopped : Beh E → Prop
  | .done .. => True
  | _ => False

/-- The run did not end blocked on its environment. -/
def notBlocked : Beh E → Prop
  | .blocked _ => False
  | _ => True

/-- The events of an infinite run satisfy `p` infinitely often. -/
def InfinitelyOften (p : E → Prop) : Beh E → Prop
  | .reactive f => ∀ n, ∃ m, n ≤ m ∧ p (f m)
  | _ => False

/-- Rename the events of a run. -/
def map {F : Type} (g : E → F) : Beh E → Beh F
  | .done t s => .done (t.map g) s
  | .blocked t => .blocked (t.map g)
  | .spins t => .spins (t.map g)
  | .reactive f => .reactive (g ∘ f)

end Beh

/-- **A specification**: a property of runs. -/
abbrev Spec (E : Type) : Type := Beh E → Prop

/-- **A model**: the runs of a program, over all environments. -/
abbrev Model (E : Type) : Type := Beh E → Prop

namespace Spec

variable {E : Type}

/-- **Safety**: every finite prefix satisfies `S`. -/
def safe (S : List E → Prop) : Spec E := fun b => ∀ t, b.Prefix t → S t

/-- **Partial correctness**: if the process exits, `post` holds of its events and status. -/
def partialCorrect (post : List E → UInt8 → Prop) : Spec E
  | .done t (.exited c) => post t c
  | _ => True

/-- **Total correctness**: the process exits, and `post` holds of its events and status. -/
def totalCorrect (post : List E → UInt8 → Prop) : Spec E
  | .done t (.exited c) => post t c
  | _ => False

/-- **A specification under an assumption** on the run (on the environment, or fairness). -/
def under (A φ : Spec E) : Spec E := fun b => A b → φ b

/-- The process never crashes by its own signal. -/
def noCrash : Spec E
  | .done _ (.signaled _) => False
  | _ => True

/-- Every event is in `ok`. A safety property; `Confined` is an instance. -/
def always (ok : E → Prop) : Spec E := safe fun t => ∀ e ∈ t, ok e

end Spec

namespace Model

variable {E : Type}

/-- **Satisfaction**: every run satisfies the specification. -/
def Sat (M : Model E) (φ : Spec E) : Prop := ∀ b, M b → φ b

/-- **Refinement**: every run of `M` is a run of `N` (divergence, blocking and stops included). -/
def Refines (M N : Model E) : Prop := ∀ b, M b → N b

/-- The finite traces of a model: the prefixes of its runs. -/
def Traces (M : Model E) (t : List E) : Prop := ∃ b, M b ∧ b.Prefix t

/-- **Trace refinement**: every finite trace of `M` is one of `N`. -/
def TraceRefines (M N : Model E) : Prop := ∀ t, M.Traces t → N.Traces t

/-- **Determinism up to inputs**: two runs first differ at an input event (one the environment
chooses), and runs with the same events stop the same way. -/
def DetUpToInputs (isIn : E → Bool) (M : Model E) : Prop :=
  (∀ b b' t e e', M b → M b' → b.Prefix (t ++ [e]) → b'.Prefix (t ++ [e']) → e ≠ e' →
    isIn e = true ∧ isIn e' = true) ∧
  (∀ t s s', M (.done t s) → M (.done t s') → s = s')

/-- **Noninterference** (observational determinism, for stopped runs): two runs whose low
inputs agree have the same low outputs. A property of pairs of runs. -/
def Noninterference {α β : Type} (lowIn : List E → α) (lowOut : List E → β) (M : Model E) :
    Prop :=
  ∀ t t' s s', M (.done t s) → M (.done t' s') → lowIn t = lowIn t' → lowOut t = lowOut t'

end Model

end Silmaril.Containers
