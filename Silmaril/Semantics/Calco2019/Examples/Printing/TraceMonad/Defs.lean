module

public import Silmaril.Semantics.Calco2019.Examples.Printing.Paths.Defs

/-! # The finite and infinite trace monad -/

@[expose] public section

universe u

namespace Silmaril.Calco2019.Examples.Printing

variable {A X Y : Type u}

/-- The set presentation admits empty sets for use in the order of approximants. -/
abbrev TraceSet (A X : Type u) := Set (Trace A X)

def pureTrace (x : X) : TraceSet A X := {Sum.inl ([], x)}

/-- Extend a finite observation by a continuation. An infinite observation persists. -/
def extendTrace (k : X → TraceSet A Y) : Trace A X → TraceSet A Y
  | .inl (word, x) => prepend word '' k x
  | .inr s => {Sum.inr s}

def bindTraces (p : TraceSet A X) (k : X → TraceSet A Y) : TraceSet A Y :=
  {t | ∃ s ∈ p, t ∈ extendTrace k s}

instance : Monad (TraceSet A) where
  pure := pureTrace
  bind := bindTraces

/-- The nonempty trace monad from Example 10(5). -/
abbrev NonemptyTrace (A X : Type u) := {p : TraceSet A X // p.Nonempty}

instance : Monad (NonemptyTrace A) where
  pure x := ⟨pureTrace x, ⟨.inl ([], x), rfl⟩⟩
  bind p k := ⟨bindTraces p.1 (fun x => (k x).1), by
    obtain ⟨s, hs⟩ := p.2
    cases s with
    | inr stream => exact ⟨.inr stream, .inr stream, hs, rfl⟩
    | inl pair =>
      obtain ⟨word, x⟩ := pair
      obtain ⟨t, ht⟩ := (k x).2
      exact ⟨prepend word t, .inl (word, x), hs, t, ht, rfl⟩⟩

theorem val_tracePure (x : X) : (pure x : NonemptyTrace A X).1 = pureTrace x := rfl

theorem val_traceBind (p : NonemptyTrace A X) (k : X → NonemptyTrace A Y) :
    (p >>= k).1 = bindTraces p.1 (fun x => (k x).1) := rfl

/-- Relabel a successful result, preserving its printed word and every infinite trace. -/
def mapResult (h : X → Y) : Trace A X → Trace A Y :=
  Sum.map (Prod.map id h) id

end Silmaril.Calco2019.Examples.Printing
