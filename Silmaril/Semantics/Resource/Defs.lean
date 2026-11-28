module

/-! Relational resource operations with explicit observable write footprints. -/

@[expose] public section

namespace Silmaril.Semantics.Resource

universe s i o k v i' o'

/-- The permitted replies and post-states of an input, with the keys it
may change for each reply. An inapplicable input has no transition. -/
structure Contract (State : Type s) (Input : Type i) (Output : Type o) (Key : Type k) where
  step : Input → State → Output → State → Prop
  writes : Input → Output → List Key

variable {State : Type s} {Input : Type i} {Output : Type o} {Key : Type k}
  {Observation : Type v} {NextInput : Type i'} {NextOutput : Type o'}

/-- A valid transition preserves observations outside its declared writes. -/
def Contract.Frames (contract : Contract State Input Output Key)
    (observe : State → Key → Observation) : Prop :=
  ∀ {input before output after}, contract.step input before output after →
    ∀ key, key ∉ contract.writes input output → observe after key = observe before key

/-- An assertion is determined by observations at the listed keys. -/
def DependsOn (observe : State → Key → Observation) (reads : List Key)
    (assertion : State → Prop) : Prop :=
  ∀ ⦃before after⦄, (∀ key ∈ reads, observe after key = observe before key) →
    (assertion before ↔ assertion after)

/-- Sequence two operations, computing the second input from the first
input and reply. Both replies determine the combined write footprint. -/
def Contract.seq (first : Contract State Input Output Key)
    (second : Contract State NextInput NextOutput Key)
    (next : Input → Output → NextInput) : Contract State Input (Output × NextOutput) Key where
  step input before reply after :=
    ∃ middle, first.step input before reply.1 middle ∧
      second.step (next input reply.1) middle reply.2 after
  writes input reply :=
    first.writes input reply.1 ++ second.writes (next input reply.1) reply.2

end Silmaril.Semantics.Resource
