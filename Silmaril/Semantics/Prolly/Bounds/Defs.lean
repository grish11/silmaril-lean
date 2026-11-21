module

public import Silmaril.Semantics.Prolly.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card

@[expose] public section

namespace Silmaril.Semantics.Prolly

variable {Sample Key : Type}

/-- A finite uniform experiment selects one policy, with fixed width and a
sample-dependent bucket. Equal keys use the same draw at a given level. No
independence is assumed. Marginals below are for fixed inputs. -/
structure UniformBuckets (Sample Key : Type) where
  width : Nat
  minWidth : 2 ≤ width
  hit : Sample → Nat → Key → Bool

def UniformBuckets.policy (model : UniformBuckets Sample Key) (sample : Sample) : Policy Key :=
  ⟨model.width, model.minWidth, model.hit sample⟩

def UniformBuckets.hits [Fintype Sample] (model : UniformBuckets Sample Key) (level : Nat) (key : Key) : Nat :=
  (Finset.univ.filter fun sample => model.hit sample level key = true).card

def UniformBuckets.chunks (model : UniformBuckets Sample Key) (sample : Sample) (level : Nat) (keys : List Key) : Nat :=
  (chunk ((model.policy sample).cut level) keys).length

def selectionFiber [Fintype Sample] [DecidableEq Key] (select : Sample → List Key) (keys : List Key) : Finset Sample :=
  Finset.univ.filter fun sample => select sample = keys

/-- Condition on the entire realized input list, not just on whether an individual
key is reached. `numerator / denominator` bounds the hit probability of each key
within every nonempty fiber. Empty fibers satisfy the count condition vacuously. -/
def UniformBuckets.ConditionalCap [Fintype Sample] [DecidableEq Key] (model : UniformBuckets Sample Key)
    (level : Nat) (select : Sample → List Key) (numerator denominator : Nat) : Prop :=
  0 < denominator ∧ ∀ keys key, key ∈ keys →
    denominator * ((selectionFiber select keys).filter fun sample => model.hit sample level key = true).card ≤
      numerator * (selectionFiber select keys).card

end Silmaril.Semantics.Prolly
