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

end Silmaril.Elgot
