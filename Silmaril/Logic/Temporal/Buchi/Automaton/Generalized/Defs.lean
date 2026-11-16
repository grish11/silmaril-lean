module

public import Silmaril.Logic.Temporal.Buchi.Automaton.Symbolic
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section
noncomputable section
open Classical
namespace Silmaril.Logic.Temporal.Buchi.Automaton.Generalized

/-- Finite symbolic transitions with a finite family of fairness requirements. -/
structure Symbolic (Atom : Type) (n k : Nat) where
  initial : Set (Fin n)
  guard : Fin n → Fin n → Guard Atom
  accepting : Fin k → Set (Fin n)

/-- All requirements refer to this same infinite run. An empty family is vacuous. -/
def Symbolic.Recurrent {Atom : Type} {n k : Nat} (A : Symbolic Atom n k)
    (r : Nat → Fin n) : Prop :=
  ∀ i, ∀ t, ∃ u, t ≤ u ∧ r u ∈ A.accepting i

def Symbolic.IsRun {Atom : Type} {n k : Nat} (A : Symbolic Atom n k)
    (word : Nat → Atom → Prop) (r : Nat → Fin n) : Prop :=
  ∀ t, (A.guard (r t) (r (t+1))).Holds (word t)

def Symbolic.Accepts {Atom : Type} {n k : Nat} (A : Symbolic Atom n k)
    (word : Nat → Atom → Prop) : Prop :=
  ∃ r, r 0 ∈ A.initial ∧ A.IsRun word r ∧ A.Recurrent r

def Symbolic.AcceptsPath {Atom W : Type} {n k : Nat} (A : Symbolic Atom n k)
    (R : W → W → Prop) (label : W → Atom → Prop) (w : W) : Prop :=
  ∃ p, IsPath R w p ∧ A.Accepts (label ∘ p)

/-- Phases below k await that requirement. Phase k marks a completed round;
its next step resets to zero, still consuming the ordinary source letter. -/
def advance {k : Nat} (hit : Fin k → Prop) (c : Fin (k+1)) : Fin (k+1) :=
  if h : c.val < k then
    if hit ⟨c.val, h⟩ then ⟨c.val+1, by omega⟩ else c
  else 0

/-- The actual deterministic monitor on a fixed run; phase zero initially. -/
def counter {k : Nat} (hit : Nat → Fin k → Prop) : Nat → Fin (k+1)
  | 0 => 0
  | t+1 => advance (hit t) (counter hit t)

/-- Pack the source state and finite monitor into the existing Fin-state API. -/
def stateEquiv (n k : Nat) : Fin n × Fin (k+1) ≃ Fin (n*(k+1)) :=
  finProdFinEquiv

/-- Ordinary symbolic automaton. Every transition, including a sentinel reset,
still requires the original source-state guard. -/
def Symbolic.compile {Atom : Type} {n k : Nat} (A : Symbolic Atom n k) :
    Automaton.Symbolic Atom (n*(k+1)) where
  initial := {x | ((stateEquiv n k).symm x).1 ∈ A.initial ∧
    ((stateEquiv n k).symm x).2 = 0}
  guard x y :=
    let q := (stateEquiv n k).symm x
    let r := (stateEquiv n k).symm y
    if r.2 = advance (fun i => q.1 ∈ A.accepting i) q.2 then A.guard q.1 r.1 else .bot
  accepting := {x | ((stateEquiv n k).symm x).2.val = k}

/-- Atom renaming changes guards only; fairness sets and state choices persist. -/
def Symbolic.map {Atom Atom' : Type} {n k : Nat} (A : Symbolic Atom n k)
    (f : Atom → Atom') : Symbolic Atom' n k where
  initial := A.initial
  guard q r := (A.guard q r).map f
  accepting := A.accepting

end Silmaril.Logic.Temporal.Buchi.Automaton.Generalized
