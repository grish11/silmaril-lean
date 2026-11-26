module

public import Mathlib.Data.List.OfFn

/-! # Partial sequences and their finite observations -/

@[expose] public section

namespace Silmaril.Semantics.ConcurrentTrace

universe u v w z

/-- A sequence can stop supplying events without a result, return a result after a finite
word, or keep supplying events. A pending word represents available observations only. -/
inductive PartialSequence (E : Type u) (R : Type v) where
  | pending (word : List E)
  | done (word : List E) (result : R)
  | infinite (events : Nat → E)

namespace PartialSequence

variable {E : Type u} {R : Type v} {F : Type w} {S : Type z}

/-- Package a finite word with its optional result. -/
def finite (w : List E) (r : Option R) : PartialSequence E R :=
  r.elim (.pending w) (.done w)

/-- Observe at most `n` events in their sequential order. -/
def cut (s : PartialSequence E R) (n : Nat) : List E :=
  match s with
  | .pending w | .done w _ => w.take n
  | .infinite events => List.ofFn (fun i : Fin n => events i)

/-- A raw finite word is observed when the cut at its length is exactly that word. -/
def HasPrefix (s : PartialSequence E R) (word : List E) : Prop :=
  s.cut word.length = word

/-- Observe whether the sequence has completed, and its result if it has. -/
def completion : PartialSequence E R → Option R
  | .done _ r => some r
  | .pending _ | .infinite _ => none

/-- Relabel events pointwise and map successful results. -/
def map (f : E → F) (g : R → S) : PartialSequence E R → PartialSequence F S
  | .pending w => .pending (w.map f)
  | .done w r => .done (w.map f) (g r)
  | .infinite events => .infinite (f ∘ events)

end PartialSequence

/-- Finite observations indexed by a depth bound. A cut shorter than its bound certifies
that no further events can appear. A result is allowed only in that case. -/
structure PrefixSequence (E : Type u) (R : Type v) where
  cut : Nat → List E
  length_le : ∀ n, (cut n).length ≤ n
  take_eq : ∀ {m n}, m ≤ n → (cut n).take m = cut m
  completion : Option R
  completion_bounded : completion.isSome → ∃ n, (cut n).length < n

end Silmaril.Semantics.ConcurrentTrace
