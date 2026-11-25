module

public import Mathlib.Data.Set.Insert

/-! # Writer and infinite trace examples from CALCO 2019 -/

@[expose] public section

namespace Silmaril.Calco2019.Examples.Printing

universe u v w

variable {A : Type u} {X : Type v} {Y : Type w} {Z : Type*}

/-- The writer guard from Example 10(4). Each recursive step prints a nonempty word. -/
def WriterGuarded (f : X → List A × (Y ⊕ Z)) : Prop :=
  ∀ x z, (f x).2 = .inr z → (f x).1 ≠ []

/-- The right-hand side of the writer fixpoint equation. -/
def writerStep (f : X → List A × (Y ⊕ X)) (g : X → List A × Y) (x : X) : List A × Y :=
  match f x with
  | (word, .inl y) => (word, y)
  | (word, .inr x') => (word ++ (g x').1, (g x').2)

/-- The extension by the singleton action of Example 20(4). A complete divergence
discards output. -/
def writerWithDivergenceStep (f : X → List A × (Y ⊕ X))
    (g : X → Option (List A × Y)) (x : X) : Option (List A × Y) :=
  match f x with
  | (word, .inl y) => some (word, y)
  | (word, .inr x') => (g x').map fun (suffix, y) => (word ++ suffix, y)

/-- The loop that prints the same letter before every recursive call. -/
def writerForever (a : A) : Unit → List A × (Unit ⊕ Unit) := fun x => ([a], .inr x)

/-- A successful finite trace or an infinite stream of printed letters. -/
abbrev Trace (A : Type u) (Y : Type w) := (List A × Y) ⊕ (ℕ → A)

def cons (a : A) (s : ℕ → A) : ℕ → A
  | 0 => a
  | n + 1 => s n

/-- Prefix a trace by a finite word. -/
def prepend (word : List A) : Trace A Y → Trace A Y
  | .inl (suffix, y) => .inl (word ++ suffix, y)
  | .inr stream => .inr (word.foldr cons stream)

/-- The guard from Example 10(5). Every finite trace to a recursive result prints a letter. -/
def TraceGuarded (f : X → Set (Trace A (Y ⊕ Z))) : Prop :=
  ∀ x z word, Sum.inl (word, Sum.inr z) ∈ f x → word ≠ []

/-- Unfold one trace-producing step, prefixing each continuation by its printed word. -/
def traceStep (f : X → Set (Trace A (Y ⊕ X))) (g : X → Set (Trace A Y)) (x : X) :
    Set (Trace A Y) :=
  {t | (∃ word y, Sum.inl (word, Sum.inl y) ∈ f x ∧ t = .inl (word, y)) ∨
       (∃ stream, Sum.inr stream ∈ f x ∧ t = .inr stream) ∨
       (∃ word x' tail, Sum.inl (word, Sum.inr x') ∈ f x ∧ tail ∈ g x' ∧ t = prepend word tail)}

/-- The separating equation of Example 20(5) offers immediate return or another letter. -/
def traceLoop (a : A) (_ : Unit) : Set (Trace A (Unit ⊕ Unit)) :=
  {Sum.inl ([], Sum.inl ()), Sum.inl ([a], Sum.inr ())}

/-- The finite-only solution of the separating equation. -/
def finiteSolution (a : A) (_ : Unit) : Set (Trace A Unit) :=
  {t | ∃ n : ℕ, t = Sum.inl (List.replicate n a, ())}

/-- The solution that also records the infinite run. -/
def productiveSolution (a : A) (x : Unit) : Set (Trace A Unit) :=
  insert (Sum.inr fun _ => a) (finiteSolution a x)

end Silmaril.Calco2019.Examples.Printing
