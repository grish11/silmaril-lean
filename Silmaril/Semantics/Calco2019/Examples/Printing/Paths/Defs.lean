module

public import Silmaril.Semantics.Calco2019.Examples.Printing.Thms
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Order.FixedPoints

/-! # Finite and productive executions of the CALCO trace loop -/

@[expose] public section

universe u v w

namespace Silmaril.Calco2019.Examples.Printing

variable {A : Type u} {X : Type v} {Y : Type w}

/-- A finite sequence of recursive calls ending with a return or an explicit infinite trace. -/
inductive FiniteTraceRun (f : X → Set (Trace A (Y ⊕ X))) : X → Trace A Y → Prop
  | returns {x word y} : .inl (word, .inl y) ∈ f x → FiniteTraceRun f x (.inl (word, y))
  | streams {x stream} : .inr stream ∈ f x → FiniteTraceRun f x (.inr stream)
  | next {x x' word tail} : .inl (word, .inr x') ∈ f x → FiniteTraceRun f x' tail →
      FiniteTraceRun f x (prepend word tail)

/-- An infinite recursive execution, with one finite word for each edge. -/
structure InfiniteTracePath (f : X → Set (Trace A (Y ⊕ X))) (x : X) where
  state : ℕ → X
  word : ℕ → List A
  start : state 0 = x
  edge (i : ℕ) : .inl (word i, .inr (state (i + 1))) ∈ f (state i)

/-- Concatenate nonempty words, beginning at word `i`. Evaluating a letter either
reads the current word or moves to the next word with a smaller position. -/
def chunkStream (word : ℕ → List A) (productive : ∀ i, 0 < (word i).length)
    (i k : ℕ) : A :=
  if h : k < (word i).length then (word i)[k]
  else chunkStream word productive (i + 1) (k - (word i).length)
termination_by k
decreasing_by
  have := productive i
  omega

theorem InfiniteTracePath.productive {f : X → Set (Trace A (Y ⊕ X))} {x : X}
    (p : InfiniteTracePath f x) (hf : TraceGuarded f) (i : ℕ) : 0 < (p.word i).length :=
  List.length_pos_iff.mpr (hf _ _ _ (p.edge i))

/-- The infinite concatenation in the third clause of Example 20(5). -/
def InfiniteTracePath.stream {f : X → Set (Trace A (Y ⊕ X))} {x : X}
    (p : InfiniteTracePath f x) (hf : TraceGuarded f) : ℕ → A :=
  chunkStream p.word (p.productive hf) 0

/-- One unfolding is monotone in its continuation. -/
def traceUnfold (f : X → Set (Trace A (Y ⊕ X))) : (X → Set (Trace A Y)) →o (X → Set (Trace A Y)) where
  toFun := traceStep f
  monotone' := by
    intro g h legh x t ht
    rcases ht with done | stream | ⟨word, x', tail, edge, hit, rfl⟩
    · exact Or.inl done
    · exact Or.inr (Or.inl stream)
    · exact Or.inr (Or.inr ⟨word, x', tail, edge, legh x' hit, rfl⟩)

/-- The greatest set-valued fixpoint of the trace unfolding. The guard will
identify its members with the finite and productive executions of the paper. -/
def greatestTrace (f : X → Set (Trace A (Y ⊕ X))) : X → Set (Trace A Y) :=
  (traceUnfold f).gfp

theorem greatestTrace_fix (f : X → Set (Trace A (Y ⊕ X))) :
    traceStep f (greatestTrace f) = greatestTrace f :=
  (traceUnfold f).map_gfp

theorem le_greatestTrace (f : X → Set (Trace A (Y ⊕ X))) {g : X → Set (Trace A Y)}
    (hg : g ≤ traceStep f g) : g ≤ greatestTrace f :=
  (traceUnfold f).le_gfp hg

end Silmaril.Calco2019.Examples.Printing
