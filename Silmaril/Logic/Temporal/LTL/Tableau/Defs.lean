module

public import Silmaril.Logic.Temporal.LTL.NNF.Thms
public import Silmaril.Logic.Temporal.Buchi.Automaton.Generalized.Modal
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Basic

@[expose] public section
noncomputable section
open Classical
namespace Silmaril.Logic.Temporal.LTL.Tableau
open Buchi.Automaton

/-- The atom-independent occurrence tree. Repeated equal subformulas have
separate occurrences; atom equality is never tested. -/
inductive Shape where
  | leaf
  | unary : Shape → Shape
  | binary : Shape → Shape → Shape

def shape {Atom : Type} : NNF.Formula Atom → Shape
  | .pos _ | .neg _ | .bot | .top => .leaf
  | .next p => .unary (shape p)
  | .conj p q | .disj p q | .until p q | .release p q => .binary (shape p) (shape q)

def Occ : Shape → Type
  | .leaf => Unit
  | .unary s => Unit ⊕ Occ s
  | .binary s t => Unit ⊕ (Occ s ⊕ Occ t)

instance occFintype : (s : Shape) → Fintype (Occ s)
  | .leaf => show Fintype Unit from inferInstance
  | .unary s => by
    letI := occFintype s
    exact (inferInstance : Fintype (Unit ⊕ Occ s))
  | .binary s t => by
    letI := occFintype s
    letI := occFintype t
    exact (inferInstance : Fintype (Unit ⊕ (Occ s ⊕ Occ t)))

instance occDecidableEq : (s : Shape) → DecidableEq (Occ s)
  | .leaf => show DecidableEq Unit from inferInstance
  | .unary s => by
    letI := occDecidableEq s
    exact (inferInstance : DecidableEq (Unit ⊕ Occ s))
  | .binary s t => by
    letI := occDecidableEq s
    letI := occDecidableEq t
    exact (inferInstance : DecidableEq (Unit ⊕ (Occ s ⊕ Occ t)))

def root : (s : Shape) → Occ s
  | .leaf => ()
  | .unary _ => .inl ()
  | .binary _ _ => .inl ()

abbrev State (s : Shape) := Occ s → Bool

def bit {s : Shape} (X : State s) : Bool := X (root s)

def unary {s : Shape} (X : State (.unary s)) : State s := fun i => X (.inr i)
def left {s t : Shape} (X : State (.binary s t)) : State s := fun i => X (.inr (.inl i))
def right {s t : Shape} (X : State (.binary s t)) : State t := fun i => X (.inr (.inr i))

/-- Independent local semantic consistency; temporal root bits refer to the
next assignment, while guards always read the current letter. -/
def Local {Atom : Type} : (p : NNF.Formula Atom) → (Atom → Prop) →
    State (shape p) → State (shape p) → Prop
  | .pos a, letter, X, _ => (bit X = true ↔ letter a)
  | .neg a, letter, X, _ => (bit X = true ↔ ¬ letter a)
  | .bot, _, X, _ => bit X = false
  | .top, _, X, _ => bit X = true
  | .next p, letter, X, Y => (bit X = bit (unary Y)) ∧ Local p letter (unary X) (unary Y)
  | .conj p q, letter, X, Y =>
      bit X = (bit (left X) && bit (right X)) ∧
        Local p letter (left X) (left Y) ∧ Local q letter (right X) (right Y)
  | .disj p q, letter, X, Y =>
      bit X = (bit (left X) || bit (right X)) ∧
        Local p letter (left X) (left Y) ∧ Local q letter (right X) (right Y)
  | .until p q, letter, X, Y =>
      bit X = (bit (right X) || (bit (left X) && bit Y)) ∧
        Local p letter (left X) (left Y) ∧ Local q letter (right X) (right Y)
  | .release p q, letter, X, Y =>
      bit X = (bit (right X) && (bit (left X) || bit Y)) ∧
        Local p letter (left X) (left Y) ∧ Local q letter (right X) (right Y)

def check {Atom : Type} (b : Bool) : Guard Atom := if b then .top else .bot

/-- Actual finite guard syntax for every assignment pair. No semantic formula
or arbitrary acceptance predicate is inserted into the guard grammar. -/
def transition {Atom : Type} : (p : NNF.Formula Atom) →
    State (shape p) → State (shape p) → Guard Atom
  | .pos a, X, _ => if bit X then .pos a else .neg a
  | .neg a, X, _ => if bit X then .neg a else .pos a
  | .bot, X, _ => check (!bit X)
  | .top, X, _ => check (bit X)
  | .next p, X, Y => .conj (check (bit X == bit (unary Y)))
      (transition p (unary X) (unary Y))
  | .conj p q, X, Y => .conj (check (bit X == (bit (left X) && bit (right X))))
      (.conj (transition p (left X) (left Y)) (transition q (right X) (right Y)))
  | .disj p q, X, Y => .conj (check (bit X == (bit (left X) || bit (right X))))
      (.conj (transition p (left X) (left Y)) (transition q (right X) (right Y)))
  | .until p q, X, Y => .conj (check (bit X == (bit (right X) || (bit (left X) && bit Y))))
      (.conj (transition p (left X) (left Y)) (transition q (right X) (right Y)))
  | .release p q, X, Y => .conj (check (bit X == (bit (right X) && (bit (left X) || bit Y))))
      (.conj (transition p (left X) (left Y)) (transition q (right X) (right Y)))

/-- Non-until occurrences impose the trivially full accepting set. An until
occurrence is discharged when inactive or its right operand is active. -/
def discharged {Atom : Type} : (p : NNF.Formula Atom) → State (shape p) → Occ (shape p) → Prop
  | .pos _, _, _ | .neg _, _, _ | .bot, _, _ | .top, _, _ => True
  | .next _, _, .inl _ => True
  | .next p, X, .inr i => discharged p (unary X) i
  | .conj _ _, _, .inl _ | .disj _ _, _, .inl _ | .release _ _, _, .inl _ => True
  | .until _ _, X, .inl _ => bit X = false ∨ bit (right X) = true
  | .conj p _q, X, .inr (.inl i) | .disj p _q, X, .inr (.inl i) |
      .until p _q, X, .inr (.inl i) | .release p _q, X, .inr (.inl i) => discharged p (left X) i
  | .conj _p q, X, .inr (.inr i) | .disj _p q, X, .inr (.inr i) |
      .until _p q, X, .inr (.inr i) | .release _p q, X, .inr (.inr i) => discharged q (right X) i

def Fair {Atom : Type} (p : NNF.Formula Atom) (run : Nat → State (shape p)) : Prop :=
  ∀ i t, ∃ u, t ≤ u ∧ discharged p (run u) i

def stateEquiv (s : Shape) : State s ≃ Fin (Fintype.card (State s)) := Fintype.equivFin _
def occurrenceEquiv (s : Shape) : Occ s ≃ Fin (Fintype.card (Occ s)) := Fintype.equivFin _

/-- Pack any occurrence-indexed guard table and accepting family into the
existing finite-state interface. The packing depends only on erased shape. -/
def pack {Atom : Type} (s : Shape) (edge : State s → State s → Guard Atom)
    (accept : State s → Occ s → Prop) :
    Generalized.Symbolic Atom (Fintype.card (State s)) (Fintype.card (Occ s)) where
  initial := {q | bit ((stateEquiv s).symm q) = true}
  guard q r := edge ((stateEquiv s).symm q) ((stateEquiv s).symm r)
  accepting i := {q | accept ((stateEquiv s).symm q) ((occurrenceEquiv s).symm i)}

/-- A concrete finite generalized symbolic automaton, with one finite guard for
every pair of Boolean occurrence assignments. -/
def automaton {Atom : Type} (p : NNF.Formula Atom) :
    Generalized.Symbolic Atom (Fintype.card (State (shape p))) (Fintype.card (Occ (shape p))) :=
  pack (shape p) (transition p) (discharged p)

/-- The actual subformula at each occurrence, retaining repeated occurrences. -/
def subformula {Atom : Type} : (p : NNF.Formula Atom) → Occ (shape p) → NNF.Formula Atom
  | p@(.pos _), _ | p@(.neg _), _ | p@(.bot), _ | p@(.top), _ => p
  | p@(.next _), .inl _ => p
  | .next p, .inr i => subformula p i
  | p@(.conj _ _), .inl _ | p@(.disj _ _), .inl _ |
      p@(.until _ _), .inl _ | p@(.release _ _), .inl _ => p
  | .conj p _q, .inr (.inl i) | .disj p _q, .inr (.inl i) |
      .until p _q, .inr (.inl i) | .release p _q, .inr (.inl i) => subformula p i
  | .conj _p q, .inr (.inr i) | .disj _p q, .inr (.inr i) |
      .until _p q, .inr (.inr i) | .release _p q, .inr (.inr i) => subformula q i

/-- Completeness uses this canonical truth assignment. Soundness for arbitrary
runs will only claim that active bits imply truth. -/
def truth {Atom : Type} (p : NNF.Formula Atom) (word : Nat → Atom → Prop) (t : Nat) :
    State (shape p) := fun i => decide ((subformula p i).Holds word t)

end Silmaril.Logic.Temporal.LTL.Tableau
