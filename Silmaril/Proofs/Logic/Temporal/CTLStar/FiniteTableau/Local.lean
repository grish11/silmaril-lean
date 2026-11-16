module

public import Silmaril.Logic.Temporal.CTLStar.FiniteTableau.Defs

@[expose] public section
noncomputable section
open Classical
namespace Silmaril.Logic.Temporal.CTLStar.FiniteTableau
open LTL.Tableau Buchi.Automaton

private theorem check_holds' {A : Type} (b : Bool) (letter : A → Prop) :
    (check b).Holds letter ↔ b = true := by
  cases b <;> simp [check, Guard.Holds]

theorem transition_holds {A : Type} (p : NNF.Formula A) (letter : A → Prop)
    (X Y : State (shape p)) : (transition p X Y).Holds letter ↔ Local p letter X Y := by
  induction p with
  | pos a => cases h : bit X <;> simp [transition, Local, Guard.Holds, h]
  | neg a => cases h : bit X <;> simp [transition, Local, Guard.Holds, h]
  | bot => simp [transition, Local, check_holds']
  | top => exact check_holds' _ _
  | strongNext p ih | weakNext p ih =>
      simp only [transition, Guard.Holds, check_holds', beq_iff_eq, ih, Local]
  | conj p q hp hq | disj p q hp hq | «until» p q hp hq | release p q hp hq =>
      simp only [transition, Guard.Holds, check_holds', beq_iff_eq, hp, hq, Local]

theorem terminal_holds {A : Type} (p : NNF.Formula A) (letter : A → Prop)
    (X : State (shape p)) : (terminal p X).Holds letter ↔ End p letter X := by
  induction p with
  | pos a => cases h : bit X <;> simp [terminal, End, Guard.Holds, h]
  | neg a => cases h : bit X <;> simp [terminal, End, Guard.Holds, h]
  | bot => simp [terminal, End, check_holds']
  | top => exact check_holds' _ _
  | strongNext p ih => simp only [terminal, Guard.Holds, check_holds', Bool.not_eq_true', ih, End]
  | weakNext p ih => simp only [terminal, Guard.Holds, check_holds', ih, End]
  | conj p q hp hq | disj p q hp hq | «until» p q hp hq | release p q hp hq =>
      simp only [terminal, Guard.Holds, check_holds', beq_iff_eq, hp, hq, End]

@[simp] theorem subformula_root {A : Type} (p : NNF.Formula A) :
    subformula p (root (shape p)) = p := by cases p <;> rfl

@[simp] theorem truth_bit {A : Type} (p : NNF.Formula A) (n : Nat)
    (word : Nat → A → Prop) (t : Nat) :
    bit (truth p n word t) = true ↔ p.Holds (some n) word t := by
  simp [truth, bit]

@[simp] theorem truth_strongNext {Atom : Type} (p : NNF.Formula Atom) (n : Nat) (word : Nat → Atom → Prop)
    (t : Nat) : unary (truth (.strongNext p) n word t) = truth p n word t := rfl

@[simp] theorem truth_weakNext {Atom : Type} (p : NNF.Formula Atom) (n : Nat) (word : Nat → Atom → Prop)
    (t : Nat) : unary (truth (.weakNext p) n word t) = truth p n word t := rfl

@[simp] theorem truth_conj_left {Atom : Type} (p q : NNF.Formula Atom)
    (n : Nat) (word : Nat → Atom → Prop) (t : Nat) :
    left (truth (.conj p q) n word t) = truth p n word t := rfl

@[simp] theorem truth_conj_right {Atom : Type} (p q : NNF.Formula Atom)
    (n : Nat) (word : Nat → Atom → Prop) (t : Nat) :
    right (truth (.conj p q) n word t) = truth q n word t := rfl

@[simp] theorem truth_disj_left {Atom : Type} (p q : NNF.Formula Atom)
    (n : Nat) (word : Nat → Atom → Prop) (t : Nat) :
    left (truth (.disj p q) n word t) = truth p n word t := rfl

@[simp] theorem truth_disj_right {Atom : Type} (p q : NNF.Formula Atom)
    (n : Nat) (word : Nat → Atom → Prop) (t : Nat) :
    right (truth (.disj p q) n word t) = truth q n word t := rfl

@[simp] theorem truth_until_left {Atom : Type} (p q : NNF.Formula Atom)
    (n : Nat) (word : Nat → Atom → Prop) (t : Nat) :
    left (truth (.until p q) n word t) = truth p n word t := rfl

@[simp] theorem truth_until_right {Atom : Type} (p q : NNF.Formula Atom)
    (n : Nat) (word : Nat → Atom → Prop) (t : Nat) :
    right (truth (.until p q) n word t) = truth q n word t := rfl

@[simp] theorem truth_release_left {Atom : Type} (p q : NNF.Formula Atom)
    (n : Nat) (word : Nat → Atom → Prop) (t : Nat) :
    left (truth (.release p q) n word t) = truth p n word t := rfl

@[simp] theorem truth_release_right {Atom : Type} (p q : NNF.Formula Atom)
    (n : Nat) (word : Nat → Atom → Prop) (t : Nat) :
    right (truth (.release p q) n word t) = truth q n word t := rfl

end Silmaril.Logic.Temporal.CTLStar.FiniteTableau
