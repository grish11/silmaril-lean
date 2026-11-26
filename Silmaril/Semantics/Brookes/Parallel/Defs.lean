module

public import Silmaril.Semantics.Brookes.Defs

@[expose] public section

namespace Silmaril.Semantics.Brookes.Behavior

universe u v w

variable {Store : Type u} {A : Type v} {B : Type w}

/-- Apply a pure function to the terminal result of each word. -/
def mapResult (f : A → B) (behavior : Behavior Store A) : Behavior Store B where
  accepts trace result := ∃ a, behavior.accepts trace a ∧ f a = result
  nonempty := by
    rintro _ _ ⟨_, h, _⟩
    exact behavior.nonempty h
  stable := by
    rintro _ _ _ ⟨a, h, eq⟩ step
    exact ⟨a, behavior.stable h step, eq⟩

/-- Interleave the operands on the same store, pair their terminal results,
and close the resulting words under stuttering and mumbling. -/
def parallel (first : Behavior Store A) (second : Behavior Store B) : Behavior Store (A × B) :=
  generate fun trace result =>
    ∃ left right, first.accepts left result.1 ∧ second.accepts right result.2 ∧
      Shuffle left right trace

/-- Pair a computation's result with a fixed pure context. -/
def strength (context : A) (behavior : Behavior Store B) : Behavior Store (A × B) :=
  behavior.mapResult (fun result => (context, result))

end Silmaril.Semantics.Brookes.Behavior
