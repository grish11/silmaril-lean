module

public import Mathlib.Control.Monad.Writer
public import Mathlib.Data.Set.Functor
public import Silmaril.Machine.Trace
public import Silmaril.Semantics.ConcurrentTrace.Defs

/-! # Finite executions of a current-thread virtual machine -/

@[expose] public section

namespace Silmaril.Machine.MulticoreVM

open Silmaril.Semantics.ConcurrentTrace (LocalLetter Word ofWord)

universe u

/-- A step emits events of its current thread and synchronization participant lists.
An empty fragment represents a silent step. -/
abbrev Fragment (Thread Event : Type u) := List (LocalLetter Thread Event)

/-- Give each event in the fragment its current thread's name. -/
def nameFragment {Thread Event : Type u} (thread : Thread)
    (fragment : Fragment Thread Event) : Word Thread Event :=
  fragment.map fun
    | .event value => .event thread value
    | .sync participants => .sync participants

/-- A current-thread transition can admit several outcomes for a fixed thread and choice.
Use `Unit` for choices that the scheduler leaves entirely to the step relation. -/
abbrev Transition (State Thread Choice Event : Type u) :=
  Thread → Choice → State → Fragment Thread Event → State → Prop

/-- One scheduler decision fixes a thread and an auxiliary input to the transition. -/
structure Decision (Thread Choice : Type u) where
  thread : Thread
  choice : Choice

abbrev Schedule (Thread Choice : Type u) := List (Decision Thread Choice)
abbrev Outcome (State Thread Event : Type u) := State × Word Thread Event

variable {State Thread Choice Event : Type u}

/-- Successful runs of a fixed finite schedule. Every entry must take a transition. -/
inductive Scheduled (step : Transition State Thread Choice Event) :
    Schedule Thread Choice → State → Word Thread Event → State → Prop
  | nil (state : State) : Scheduled step [] state [] state
  | cons {decision schedule initial next final fragment tail} :
      step decision.thread decision.choice initial fragment next →
      Scheduled step schedule next tail final →
      Scheduled step (decision :: schedule) initial
        (nameFragment decision.thread fragment ++ tail) final

/-- One named transition with the scheduler decision hidden. -/
def machineStep (step : Transition State Thread Choice Event)
    (initial : State) (word : Word Thread Event) (final : State) : Prop :=
  ∃ thread choice fragment,
    step thread choice initial fragment final ∧ word = nameFragment thread fragment

/-- State and a chronological word, over the powerset of possible returns.
The state transformer passes each branch's state to its own continuation. -/
abbrev Computation (State Thread Event : Type u) :=
  StateT State (WriterT (Word Thread Event) SetM)

/-- Interpret a relation step by choosing any available scheduler decision and outcome. -/
def anyStep (step : Transition State Thread Choice Event) : Computation State Thread Event PUnit :=
  fun initial => WriterT.mk
    { p | machineStep step initial p.2 p.1.2 }

/-- The monadic run of exactly this many transitions. A blocked branch contributes no result. -/
def run (step : Transition State Thread Choice Event) : Nat → Computation State Thread Event PUnit
  | 0 => pure ⟨⟩
  | n + 1 => anyStep step >>= fun _ => run step n

/-- The named observation returns the final state and the entire chronological word. -/
def namedOutcomes (run : Computation State Thread Event PUnit) (initial : State) :
    Set (Outcome State Thread Event) :=
  { p | ((⟨⟩, p.1), p.2) ∈ (WriterT.run (run.run initial)).run }

/-- The outcome set of a fixed schedule, in the named observation. -/
def scheduledOutcomes (step : Transition State Thread Choice Event)
    (schedule : Schedule Thread Choice) (initial : State) : Set (Outcome State Thread Event) :=
  { p | Scheduled step schedule initial p.2 p.1 }

/-- The pure state observation forgets the emitted word. -/
def observePure : Outcome State Thread Event → State := Prod.fst

/-- The concurrent observation retains the final state and quotients the named word. -/
def observeQuotient (outcome : Outcome State Thread Event) :
    State × Semantics.ConcurrentTrace.Trace Thread Event :=
  (outcome.1, ofWord outcome.2)

/-- Read a deterministic partial executor as a transition relation. -/
def ofExecutor
    (exec : Thread → Choice → State → Option (State × Fragment Thread Event)) :
    Transition State Thread Choice Event :=
  fun thread choice initial fragment final => exec thread choice initial = some (final, fragment)

/-- Execute a finite schedule with a partial step function, returning its named observation. -/
def execute (exec : Thread → Choice → State → Option (State × Fragment Thread Event)) :
    Schedule Thread Choice → State → Option (Outcome State Thread Event)
  | [], initial => some (initial, [])
  | decision :: schedule, initial => do
    let (next, fragment) ← exec decision.thread decision.choice initial
    let (final, tail) ← execute exec schedule next
    return (final, nameFragment decision.thread fragment ++ tail)

end Silmaril.Machine.MulticoreVM
