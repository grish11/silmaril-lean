module

public import Silmaril.Logic.Institution.Basic
public import Mathlib.CategoryTheory.Discrete.Basic

/-! # Sentence fragments over an independent base language

The atom carrier is never enlarged by adding connectives. Conjunction and
disjunction lists interpret empty lists as True and False, respectively.
Satisfaction under renaming is an iff; positive-truth simulations are separate.
-/

@[expose] public section
namespace Silmaril.Logic.Fragments
universe u

abbrev Conjunction (Atom : Type u) := List Atom
abbrev Disjunction (Atom : Type u) := List Atom

def all {A : Type u} (V : A → Prop) (xs : List A) : Prop := ∀ a ∈ xs, V a
def any {A : Type u} (V : A → Prop) (xs : List A) : Prop := ∃ a ∈ xs, V a

inductive Positive (A : Type u) where
  | atom (a : A)
  | truth | falsehood
  | conj (p q : Positive A)
  | disj (p q : Positive A)

def Positive.map {A B : Type u} (f : A → B) : Positive A → Positive B
  | .atom a => .atom (f a)
  | .truth => .truth
  | .falsehood => .falsehood
  | .conj p q => .conj (p.map f) (q.map f)
  | .disj p q => .disj (p.map f) (q.map f)

def Positive.eval {A : Type u} (V : A → Prop) : Positive A → Prop
  | .atom a => V a
  | .truth => True
  | .falsehood => False
  | .conj p q => p.eval V ∧ q.eval V
  | .disj p q => p.eval V ∨ q.eval V

/-- Conjunction plus negation; disjunction is a derived operation. -/
inductive ConjNeg (A : Type u) where
  | atom (a : A)
  | truth
  | conj (p q : ConjNeg A)
  | neg (p : ConjNeg A)

def ConjNeg.map {A B : Type u} (f : A → B) : ConjNeg A → ConjNeg B
  | .atom a => .atom (f a)
  | .truth => .truth
  | .conj p q => .conj (p.map f) (q.map f)
  | .neg p => .neg (p.map f)

def ConjNeg.eval {A : Type u} (V : A → Prop) : ConjNeg A → Prop
  | .atom a => V a
  | .truth => True
  | .conj p q => p.eval V ∧ q.eval V
  | .neg p => ¬ p.eval V

def ConjNeg.disj {A : Type u} (p q : ConjNeg A) : ConjNeg A := .neg (.conj (.neg p) (.neg q))

def Positive.toConjNeg {A : Type u} : Positive A → ConjNeg A
  | .atom a => .atom a
  | .truth => .truth
  | .falsehood => .neg .truth
  | .conj p q => .conj p.toConjNeg q.toConjNeg
  | .disj p q => p.toConjNeg.disj q.toConjNeg

def conjunction {A : Type u} : Conjunction A → Positive A
  | [] => .truth
  | a :: as => .conj (.atom a) (conjunction as)

def disjunction {A : Type u} : Disjunction A → Positive A
  | [] => .falsehood
  | a :: as => .disj (.atom a) (disjunction as)

structure Literal (A : Type u) where
  positive : Bool
  atom : A

abbrev SignedConjunction (A : Type u) := List (Literal A)

def Literal.map {A B : Type u} (f : A → B) (l : Literal A) : Literal B := ⟨l.positive, f l.atom⟩
def Literal.eval {A : Type u} (V : A → Prop) (l : Literal A) : Prop :=
  if l.positive then V l.atom else ¬ V l.atom

def Literal.toConjNeg {A : Type u} (l : Literal A) : ConjNeg A :=
  if l.positive then .atom l.atom else .neg (.atom l.atom)

def signedConjunction {A : Type u} : SignedConjunction A → ConjNeg A
  | [] => .truth
  | l :: ls => .conj l.toConjNeg (signedConjunction ls)

/-- Every instance extends any base room/institution without changing models
or reducts. In particular model arrows are not silently restricted. -/
structure Fragment where
  Form : Type u → Type u
  map : {A B : Type u} → (A → B) → Form A → Form B
  eval : {A : Type u} → (A → Prop) → Form A → Prop
  map_id : ∀ {A} (p : Form A), map id p = p
  map_comp : ∀ {A B C} (f : A → B) (g : B → C) (p : Form A),
    map (g ∘ f) p = map g (map f p)
  satisfaction : ∀ {A B} (f : A → B) (V : B → Prop) (p : Form A),
    eval V (map f p) ↔ eval (V ∘ f) p

/-- A modular syntactic translation, natural in atomic renamings and exact
on satisfaction. This is independent of the model simulation order. -/
structure Translation (F G : Fragment.{u}) where
  translate : {A : Type u} → F.Form A → G.Form A
  natural : ∀ {A B} (f : A → B) (p : F.Form A),
    translate (F.map f p) = G.map f (translate p)
  satisfaction : ∀ {A} (V : A → Prop) (p : F.Form A),
    G.eval V (translate p) ↔ F.eval V p

/-- A one-way simulation of observed atomic truth. -/
def Preserves {A : Type u} (observed : Set A) (P Q : A → Prop) : Prop :=
  ∀ a ∈ observed, P a → Q a

/-- Preservation for both signs is stronger than positive preservation. -/
def PreservesSigned {A : Type u} (observed : Set A) (P Q : A → Prop) : Prop :=
  ∀ l : Literal A, l.atom ∈ observed → l.eval P → l.eval Q

def Reflects {A : Type u} (observed : Set A) (P Q : A → Prop) : Prop :=
  ∀ a ∈ observed, Q a → P a

end Silmaril.Logic.Fragments
