module

public import Silmaril.Semantics.Calco2019.Examples.Printing.Paths.Defs
import Silmaril.Proofs.Semantics.Calco2019.Examples.TracePaths

/-! # The finite and infinite clauses of Example 20(5) -/

public section

universe u v w

namespace Silmaril.Calco2019.Examples.Printing

variable {A : Type u} {X : Type v} {Y : Type w}
  {f : X → Set (Trace A (Y ⊕ X))}

/-- Concatenation respects removal of the first nonempty word. -/
theorem chunk_unfold (word : ℕ → List A) (productive : ∀ i, 0 < (word i).length) (i : ℕ) :
    chunkStream word productive i = (word i).foldr cons (chunkStream word productive (i + 1)) :=
  PathProofs.chunk_unfold word productive i

/-- The greatest solution retains every finite successful run. -/
theorem finite_sound {x : X} {t : Trace A Y} (h : FiniteTraceRun f x t) :
    t ∈ greatestTrace f x :=
  PathProofs.finite_sound h

/-- A selected infinite recursive path contributes its infinite word. -/
theorem infinite_sound {x : X} (p : InfiniteTracePath f x) (hf : TraceGuarded f) :
    Sum.inr (p.stream hf) ∈ greatestTrace f x :=
  PathProofs.infinite_sound p hf

/-- Every finite result in the greatest solution comes from a finite run. -/
theorem finite_complete (hf : TraceGuarded f) {x : X} {word : List A} {y : Y}
    (h : Sum.inl (word, y) ∈ greatestTrace f x) : FiniteTraceRun f x (.inl (word, y)) :=
  PathProofs.finite_complete hf h

/-- Guardedness excludes fictitious finite results and makes infinite recursive runs
productive. These are precisely the three clauses of Example 20(5). -/
theorem greatest_iff (hf : TraceGuarded f) (x : X) (t : Trace A Y) :
    t ∈ greatestTrace f x ↔ FiniteTraceRun f x t ∨
      ∃ p : InfiniteTracePath f x, t = Sum.inr (p.stream hf) :=
  PathProofs.greatest_iff hf x t

theorem greatest_nonempty (hf : TraceGuarded f) (hbody : ∀ x, (f x).Nonempty) (x : X) :
    (greatestTrace f x).Nonempty :=
  PathProofs.greatest_nonempty hf hbody x

/-- The chosen solution of the separating equation retains both the finite words
and the infinite repetition of the letter. -/
theorem greatest_letter_trace (a : A) : greatestTrace (traceLoop a) = productiveSolution a :=
  PathProofs.greatest_letter_trace a

end Silmaril.Calco2019.Examples.Printing
