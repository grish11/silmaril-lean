module

public import Silmaril.Semantics.Prolly.Bounds.Defs
public import Silmaril.Semantics.Prolly.Frontier.Defs

@[expose] public section

namespace Silmaril.Semantics.Prolly

open scoped BigOperators

variable {Sample Key : Type}

/-- Condition on the actual active frontier of each round, treating stopped
samples as empty. One common rational cap applies to all active rounds. -/
def UniformBuckets.FrontierCap [Fintype Sample] [DecidableEq Key] (model : UniformBuckets Sample Key)
    (keys : List Key) (numerator denominator : Nat) : Prop :=
  ∀ level, model.ConditionalCap level (fun sample =>
    activeKeys (model.policy sample) (frontierAt (model.policy sample) level 0 keys)) numerator denominator

def UniformBuckets.frontierMass [Fintype Sample] (model : UniformBuckets Sample Key)
    (keys : List Key) (steps : Nat) : Nat :=
  ∑ sample : Sample, (frontierAt (model.policy sample) steps 0 keys).length

end Silmaril.Semantics.Prolly
