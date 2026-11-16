module

public import Silmaril.Logic.Temporal.CTLStar.NNF.Thms
public import Silmaril.Logic.Temporal.LTL.Tableau.Defs

@[expose] public section
noncomputable section
open Classical
namespace Silmaril.Logic.Temporal.CTLStar.FiniteTableau
open LTL.Tableau Buchi.Automaton

def shape {Atom : Type} : NNF.Formula Atom → Shape
  | .pos _ | .neg _ | .bot | .top => .leaf
  | .strongNext p | .weakNext p => .unary (shape p)
  | .conj p q | .disj p q | .until p q | .release p q => .binary (shape p) (shape q)

def Local {Atom : Type} : (p : NNF.Formula Atom) → (Atom → Prop) →
    State (shape p) → State (shape p) → Prop
  | .pos a, letter, X, _ => (bit X = true ↔ letter a)
  | .neg a, letter, X, _ => (bit X = true ↔ ¬ letter a)
  | .bot, _, X, _ => bit X = false
  | .top, _, X, _ => bit X = true
  | .strongNext p, letter, X, Y | .weakNext p, letter, X, Y => (bit X = bit (unary Y)) ∧ Local p letter (unary X) (unary Y)
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

def transition {Atom : Type} : (p : NNF.Formula Atom) →
    State (shape p) → State (shape p) → Guard Atom
  | .pos a, X, _ => if bit X then .pos a else .neg a
  | .neg a, X, _ => if bit X then .neg a else .pos a
  | .bot, X, _ => check (!bit X)
  | .top, X, _ => check (bit X)
  | .strongNext p, X, Y | .weakNext p, X, Y => .conj (check (bit X == bit (unary Y)))
      (transition p (unary X) (unary Y))
  | .conj p q, X, Y => .conj (check (bit X == (bit (left X) && bit (right X))))
      (.conj (transition p (left X) (left Y)) (transition q (right X) (right Y)))
  | .disj p q, X, Y => .conj (check (bit X == (bit (left X) || bit (right X))))
      (.conj (transition p (left X) (left Y)) (transition q (right X) (right Y)))
  | .until p q, X, Y => .conj (check (bit X == (bit (right X) || (bit (left X) && bit Y))))
      (.conj (transition p (left X) (left Y)) (transition q (right X) (right Y)))
  | .release p q, X, Y => .conj (check (bit X == (bit (right X) && (bit (left X) || bit Y))))
      (.conj (transition p (left X) (left Y)) (transition q (right X) (right Y)))


/-- Final-letter consistency: no next assignment exists, and Until/Release
both reduce to their right operand at the real endpoint. -/
def End {A : Type} : (p : NNF.Formula A) → (A → Prop) → State (shape p) → Prop
  | .pos a, letter, X => bit X = true ↔ letter a
  | .neg a, letter, X => bit X = true ↔ ¬ letter a
  | .bot, _, X => bit X = false
  | .top, _, X => bit X = true
  | .strongNext p, letter, X => bit X = false ∧ End p letter (unary X)
  | .weakNext p, letter, X => bit X = true ∧ End p letter (unary X)
  | .conj p q, letter, X => bit X = (bit (left X) && bit (right X)) ∧
      End p letter (left X) ∧ End q letter (right X)
  | .disj p q, letter, X => bit X = (bit (left X) || bit (right X)) ∧
      End p letter (left X) ∧ End q letter (right X)
  | .until p q, letter, X | .release p q, letter, X => bit X = bit (right X) ∧
      End p letter (left X) ∧ End q letter (right X)

/-- Actual finite guard syntax, including checks at all child occurrences. -/
def terminal {A : Type} : (p : NNF.Formula A) → State (shape p) → Guard A
  | .pos a, X => if bit X then .pos a else .neg a
  | .neg a, X => if bit X then .neg a else .pos a
  | .bot, X => check (!bit X)
  | .top, X => check (bit X)
  | .strongNext p, X => .conj (check (!bit X)) (terminal p (unary X))
  | .weakNext p, X => .conj (check (bit X)) (terminal p (unary X))
  | .conj p q, X => .conj (check (bit X == (bit (left X) && bit (right X))))
      (.conj (terminal p (left X)) (terminal q (right X)))
  | .disj p q, X => .conj (check (bit X == (bit (left X) || bit (right X))))
      (.conj (terminal p (left X)) (terminal q (right X)))
  | .until p q, X | .release p q, X => .conj (check (bit X == bit (right X)))
      (.conj (terminal p (left X)) (terminal q (right X)))

def subformula {Atom : Type} : (p : NNF.Formula Atom) → Occ (shape p) → NNF.Formula Atom
  | p@(.pos _), _ | p@(.neg _), _ | p@(.bot), _ | p@(.top), _ => p
  | p@(.strongNext _), .inl _ | p@(.weakNext _), .inl _ => p
  | .strongNext p, .inr i | .weakNext p, .inr i => subformula p i
  | p@(.conj _ _), .inl _ | p@(.disj _ _), .inl _ |
      p@(.until _ _), .inl _ | p@(.release _ _), .inl _ => p
  | .conj p _q, .inr (.inl i) | .disj p _q, .inr (.inl i) |
      .until p _q, .inr (.inl i) | .release p _q, .inr (.inl i) => subformula p i
  | .conj _p q, .inr (.inr i) | .disj _p q, .inr (.inr i) |
      .until _p q, .inr (.inr i) | .release _p q, .inr (.inr i) => subformula q i


/-- Canonical truth assignment, used only to prove completeness. -/
def truth {A : Type} (p : NNF.Formula A) (n : Nat) (word : Nat → A → Prop) (t : Nat) :
    State (shape p) := fun i => decide ((subformula p i).Holds (some n) word t)

/-- A nonempty finite word has n+1 letters. Guards read exactly positions 0..n;
the final guard consumes the last letter without taking another transition. -/
def Accepts {A : Type} (p : NNF.Formula A) (n : Nat) (word : Nat → A → Prop) : Prop :=
  ∃ run : Nat → State (shape p), bit (run 0) = true ∧
    (∀ t, t < n → (transition p (run t) (run (t+1))).Holds (word t)) ∧
    (terminal p (run n)).Holds (word n)

end Silmaril.Logic.Temporal.CTLStar.FiniteTableau
