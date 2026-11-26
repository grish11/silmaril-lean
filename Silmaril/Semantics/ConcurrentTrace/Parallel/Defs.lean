module

public import Silmaril.Semantics.Brookes.Defs
public import Silmaril.Semantics.ConcurrentTrace.Defs

/-! # Free-shuffle parallel composition

A shuffle takes each occurrence from exactly one component, preserving the order of each
given word. Component origin comes from the shuffle derivation, independently of the
thread IDs and participant lists on its letters. Each synchronization letter contributes
one separate occurrence. A handshake would require rules for matching component steps.
This operation describes trace languages. VM executability requires a separate operational
semantics for thread state and shared effects.
-/

@[expose] public section

namespace Silmaril.Semantics.ConcurrentTrace

variable {T E : Type*}

/-- One legal adjacent swap at a specified position in a word. -/
inductive AdjacentSwap : Word T E → Word T E → Prop where
  | inContext {a b : Letter T E} (h : a.Independent b) (pre post : Word T E) :
      AdjacentSwap (pre ++ a :: b :: post) (pre ++ b :: a :: post)

/-- Raw interleavings of two word languages. Each step of `Brookes.Shuffle` records
the component from which the next occurrence is taken. -/
def shuffleWords (s t : Set (Word T E)) : Set (Word T E) :=
  {w | ∃ x ∈ s, ∃ y ∈ t, Brookes.Shuffle x y w}

/-- Free-shuffle product of languages of finite traces, using all representatives
of both operands. The operands may use overlapping thread IDs. -/
def parallel (s t : Set (Trace T E)) : Set (Trace T E) :=
  toTraces (shuffleWords (ofTraces s) (ofTraces t))

end Silmaril.Semantics.ConcurrentTrace
