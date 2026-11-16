module

public import Silmaril.Logic.Temporal.LTL.Tableau.Defs

@[expose] public section
noncomputable section
open Classical
namespace Silmaril.Logic.Temporal.LTL.Tableau
open Buchi.Automaton

theorem check_holds {Atom : Type} (b : Bool) (letter : Atom → Prop) :
    (check b).Holds letter ↔ b = true := by
  cases b <;> simp [check, Guard.Holds]

theorem transition_holds {Atom : Type} (p : NNF.Formula Atom) (letter : Atom → Prop)
    (X Y : State (shape p)) : (transition p X Y).Holds letter ↔ Local p letter X Y := by
  induction p with
  | pos a => cases h : bit X <;> simp [transition, Local, Guard.Holds, h]
  | neg a => cases h : bit X <;> simp [transition, Local, Guard.Holds, h]
  | bot => simp [transition, Local, check_holds]
  | top => exact check_holds _ _
  | next p ih => simp only [transition, Guard.Holds, check_holds, beq_iff_eq, ih, Local]
  | conj p q hp hq => simp only [transition, Guard.Holds, check_holds, beq_iff_eq, hp, hq, Local]
  | disj p q hp hq => simp only [transition, Guard.Holds, check_holds, beq_iff_eq, hp, hq, Local]
  | «until» p q hp hq => simp only [transition, Guard.Holds, check_holds, beq_iff_eq, hp, hq, Local]
  | release p q hp hq => simp only [transition, Guard.Holds, check_holds, beq_iff_eq, hp, hq, Local]

@[simp] theorem subformula_root {Atom : Type} (p : NNF.Formula Atom) :
    subformula p (root (shape p)) = p := by
  cases p <;> rfl

@[simp] theorem truth_bit {Atom : Type} (p : NNF.Formula Atom) (word : Nat → Atom → Prop)
    (t : Nat) : bit (truth p word t) = true ↔ p.Holds word t := by
  simp [truth, bit]

@[simp] theorem truth_unary {Atom : Type} (p : NNF.Formula Atom) (word : Nat → Atom → Prop)
    (t : Nat) : unary (truth (.next p) word t) = truth p word t := rfl

@[simp] theorem truth_conj_left {Atom : Type} (p q : NNF.Formula Atom)
    (word : Nat → Atom → Prop) (t : Nat) :
    left (truth (.conj p q) word t) = truth p word t := rfl

@[simp] theorem truth_conj_right {Atom : Type} (p q : NNF.Formula Atom)
    (word : Nat → Atom → Prop) (t : Nat) :
    right (truth (.conj p q) word t) = truth q word t := rfl

@[simp] theorem truth_disj_left {Atom : Type} (p q : NNF.Formula Atom)
    (word : Nat → Atom → Prop) (t : Nat) :
    left (truth (.disj p q) word t) = truth p word t := rfl

@[simp] theorem truth_disj_right {Atom : Type} (p q : NNF.Formula Atom)
    (word : Nat → Atom → Prop) (t : Nat) :
    right (truth (.disj p q) word t) = truth q word t := rfl

@[simp] theorem truth_until_left {Atom : Type} (p q : NNF.Formula Atom)
    (word : Nat → Atom → Prop) (t : Nat) :
    left (truth (.until p q) word t) = truth p word t := rfl

@[simp] theorem truth_until_right {Atom : Type} (p q : NNF.Formula Atom)
    (word : Nat → Atom → Prop) (t : Nat) :
    right (truth (.until p q) word t) = truth q word t := rfl

@[simp] theorem truth_release_left {Atom : Type} (p q : NNF.Formula Atom)
    (word : Nat → Atom → Prop) (t : Nat) :
    left (truth (.release p q) word t) = truth p word t := rfl

@[simp] theorem truth_release_right {Atom : Type} (p q : NNF.Formula Atom)
    (word : Nat → Atom → Prop) (t : Nat) :
    right (truth (.release p q) word t) = truth q word t := rfl

end Silmaril.Logic.Temporal.LTL.Tableau
