module

public import Silmaril.Semantics.Elgot.Defs

/-! # Partition feedback between two nested iterators -/

@[expose] public section

namespace Silmaril.Elgot

universe u v

/-- At an inner state, keep the original feedback in the inner iterator.
At an outer state, pass the body's result and any feedback to the outer iterator. -/
def partitionStep {m : Type u → Type v} [Functor m] {A B : Type u}
    (body : A → m (B ⊕ A)) (inner : A → Bool) (state : A) : m ((B ⊕ A) ⊕ A) :=
  if inner state then Sum.map Sum.inl id <$> body state else Sum.inl <$> body state

/-- Route feedback according to the destination state. An exit is always
returned to the outer iterator. -/
def partitionTransfer {A B : Type u} (inner : A → Bool) : B ⊕ A → (B ⊕ A) ⊕ A
  | .inl result => .inl (.inl result)
  | .inr next => if inner next then .inr next else .inl (.inr next)

def partitionStepByTarget {m : Type u → Type v} [Functor m] {A B : Type u}
    (body : A → m (B ⊕ A)) (inner : A → Bool) (state : A) : m ((B ⊕ A) ⊕ A) :=
  partitionTransfer inner <$> body state

end Silmaril.Elgot
