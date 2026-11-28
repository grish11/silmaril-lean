module

public import Silmaril.Semantics.ITree.Reindex.Defs

@[expose] public section

namespace Silmaril.Elgot.ITree

universe u v w

variable {E : Type u → Type u} {X : Type w} {A : Type v}

/-- Inclusion at one initial handler state. Observations retain exact typed
exchanges, pending requests, prefixes, and returned values. -/
def HandledTraceLE (step : Handler X E) (x : X) (t s : Tree E A) : Prop :=
  ∀ p, HandledTrace step x t p → HandledTrace step x s p

/-- A return reached by completed exchanges, with a particular possible replay
state at the return. Silent steps are already hidden by the weak tree. -/
inductive ReturnsTo (step : Handler X E) : X → Tree E A → X → A → Prop where
  | ret (x : X) (a : A) : ReturnsTo step x (ret a) x a
  | exchange {R : Type u} {e : E R} {k : R → Tree E A} {r : R} {x y z : X} {a : A} :
      step ⟨R, e⟩ x r y → ReturnsTo step y (k r) z a → ReturnsTo step x (vis e k) z a

end Silmaril.Elgot.ITree
