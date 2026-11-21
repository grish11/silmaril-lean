module

public import Silmaril.Semantics.Operational.Determinism.Defs

@[expose] public section

namespace Silmaril.Semantics.Operational

variable {S O : Type*}

inductive Stop (O : Type*) where
  | observed (outcome : Outcome O)
  | stuck
  | ub
  | unknown

def Stop.Valid (sem : WithUB S O) (source : S) : Stop O → Prop
  | .observed outcome => sem.observe source outcome
  | .stuck => sem.toOpSem.Normal source ∧ ∀ outcome, ¬ sem.observe source outcome
  | .ub => sem.ub source
  | .unknown => True

inductive Decision (S O : Type*) where
  | move (target : S)
  | stop (event : Stop O)

def Decision.Valid (sem : WithUB S O) (source : S) : Decision S O → Prop
  | .move target => sem.step source target
  | .stop event => event.Valid sem source

/-- A sound executable selection, not a new definition of the source relation.
It may report unknown; it does not silently exclude other relational paths. -/
structure Oracle (sem : WithUB S O) where
  pick : S → Decision S O
  valid : ∀ source, (pick source).Valid sem source

inductive Bounded (S O : Type*) where
  | stop (final : S) (event : Stop O)
  | exhausted (current : S)

namespace Oracle

variable {sem : WithUB S O}

/-- Execute a guard only when given its decision procedure. Negative guard
evidence, not an unknown choice or a time limit, justifies the UB answer. -/
def guard (oracle : Oracle sem) (good : S → Prop) [DecidablePred good] : Oracle (sem.enforce good) where
  pick source := if good source then oracle.pick source else .stop .ub
  valid source := by
    by_cases accepts : good source
    · simp [accepts]
      have valid := oracle.valid source
      cases selected : oracle.pick source with
      | move target => rw [selected] at valid; exact ⟨accepts, valid⟩
      | stop event =>
        rw [selected] at valid
        cases event with
        | observed outcome => exact ⟨accepts, valid⟩
        | stuck => exact ⟨fun _ step => valid.1 _ step.2, fun _ obs => valid.2 _ obs.2⟩
        | ub => exact Or.inl valid
        | unknown => trivial
    · simp [accepts, Decision.Valid, Stop.Valid, WithUB.enforce]

/-- Check the current decision before spending fuel. Only transitions consume
fuel; exhausted means another selected step exists, not that a run diverges. -/
def run (oracle : Oracle sem) (source : S) (fuel : Nat) : Bounded S O :=
  match oracle.pick source with
  | .stop event => .stop source event
  | .move target =>
    match fuel with
    | 0 => .exhausted source
    | remaining + 1 => oracle.run target remaining

end Oracle

/-- A sized prefix of the actual primitive relation. -/
inductive StepsN (step : S → S → Prop) : Nat → S → S → Prop where
  | nil (source : S) : StepsN step 0 source source
  | cons {length source next final} : step source next → StepsN step length next final →
      StepsN step (length + 1) source final

def Bounded.Sound (sem : WithUB S O) (source : S) (fuel : Nat) : Bounded S O → Prop
  | .stop final event => ∃ length, length ≤ fuel ∧ StepsN sem.step length source final ∧ event.Valid sem final
  | .exhausted current => StepsN sem.step fuel source current ∧ ∃ target, sem.step current target

end Silmaril.Semantics.Operational
