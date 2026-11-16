module

public import Silmaril.Proofs.Logic.Temporal.CTLStar.FiniteTableau.Language
public import Silmaril.Logic.Temporal.LTL.Tableau.Thms

@[expose] public section
noncomputable section
open Classical
namespace Silmaril.Logic.Temporal.CTLStar.FiniteTableau
open LTL.Tableau Buchi.Automaton

/-- Erased occurrence shape is independent of atom names, including collisions. -/
theorem shape_map {A B : Type} (f : A → B) (p : NNF.Formula A) :
    shape (p.map f) = shape p := by
  induction p <;> simp_all [NNF.Formula.map, shape]

def mapState {Atom Atom' : Type} (f : Atom → Atom') (p : NNF.Formula Atom)
    (X : State (shape p)) : State (shape (p.map f)) := castState (shape_map f p).symm X

@[simp] theorem mapState_bit {Atom Atom' : Type} (f : Atom → Atom') (p : NNF.Formula Atom)
    (X : State (shape p)) : bit (mapState f p X) = bit X := castState_bit _ _

@[simp] theorem mapState_strongNext {Atom Atom' : Type} (f : Atom → Atom') (p : NNF.Formula Atom)
    (X : State (shape (.strongNext p))) : unary (mapState f (.strongNext p) X) = mapState f p (unary X) :=
  castState_unary (shape_map f p).symm X

@[simp] theorem mapState_weakNext {Atom Atom' : Type} (f : Atom → Atom') (p : NNF.Formula Atom)
    (X : State (shape (.weakNext p))) : unary (mapState f (.weakNext p) X) = mapState f p (unary X) :=
  castState_unary (shape_map f p).symm X

@[simp] theorem check_map {Atom Atom' : Type} (f : Atom → Atom') (b : Bool) :
    (check b : Guard Atom).map f = check b := by cases b <;> rfl

@[simp] theorem mapState_conj_left {Atom Atom' : Type} (f : Atom → Atom')
    (p q : NNF.Formula Atom) (X : State (shape (.conj p q))) :
    left (mapState f (.conj p q) X) = mapState f p (left X) :=
  castState_left (shape_map f p).symm (shape_map f q).symm X

@[simp] theorem mapState_conj_right {Atom Atom' : Type} (f : Atom → Atom')
    (p q : NNF.Formula Atom) (X : State (shape (.conj p q))) :
    right (mapState f (.conj p q) X) = mapState f q (right X) :=
  castState_right (shape_map f p).symm (shape_map f q).symm X

@[simp] theorem mapState_disj_left {Atom Atom' : Type} (f : Atom → Atom')
    (p q : NNF.Formula Atom) (X : State (shape (.disj p q))) :
    left (mapState f (.disj p q) X) = mapState f p (left X) :=
  castState_left (shape_map f p).symm (shape_map f q).symm X

@[simp] theorem mapState_disj_right {Atom Atom' : Type} (f : Atom → Atom')
    (p q : NNF.Formula Atom) (X : State (shape (.disj p q))) :
    right (mapState f (.disj p q) X) = mapState f q (right X) :=
  castState_right (shape_map f p).symm (shape_map f q).symm X

@[simp] theorem mapState_until_left {Atom Atom' : Type} (f : Atom → Atom')
    (p q : NNF.Formula Atom) (X : State (shape (.until p q))) :
    left (mapState f (.until p q) X) = mapState f p (left X) :=
  castState_left (shape_map f p).symm (shape_map f q).symm X

@[simp] theorem mapState_until_right {Atom Atom' : Type} (f : Atom → Atom')
    (p q : NNF.Formula Atom) (X : State (shape (.until p q))) :
    right (mapState f (.until p q) X) = mapState f q (right X) :=
  castState_right (shape_map f p).symm (shape_map f q).symm X

@[simp] theorem mapState_release_left {Atom Atom' : Type} (f : Atom → Atom')
    (p q : NNF.Formula Atom) (X : State (shape (.release p q))) :
    left (mapState f (.release p q) X) = mapState f p (left X) :=
  castState_left (shape_map f p).symm (shape_map f q).symm X

@[simp] theorem mapState_release_right {Atom Atom' : Type} (f : Atom → Atom')
    (p q : NNF.Formula Atom) (X : State (shape (.release p q))) :
    right (mapState f (.release p q) X) = mapState f q (right X) :=
  castState_right (shape_map f p).symm (shape_map f q).symm X

set_option backward.isDefEq.respectTransparency false in
/-- Literal guards and all finite Boolean consistency checks commute with atom maps. -/
theorem transition_map {Atom Atom' : Type} (f : Atom → Atom') (p : NNF.Formula Atom)
    (X Y : State (shape p)) :
    transition (p.map f) (mapState f p X) (mapState f p Y) = (transition p X Y).map f := by
  induction p with
  | pos a => cases h : bit X <;> simp [NNF.Formula.map, transition, h, Guard.map]
  | neg a => cases h : bit X <;> simp [NNF.Formula.map, transition, h, Guard.map]
  | bot => simp [NNF.Formula.map, transition]
  | top => simp [NNF.Formula.map, transition]
  | strongNext p hp | weakNext p hp => simp [NNF.Formula.map, transition, Guard.map, hp]
  | conj p q hp hq => simp [NNF.Formula.map, transition, Guard.map, hp, hq]
  | disj p q hp hq => simp [NNF.Formula.map, transition, Guard.map, hp, hq]
  | «until» p q hp hq => simp [NNF.Formula.map, transition, Guard.map, hp, hq]
  | release p q hp hq => simp [NNF.Formula.map, transition, Guard.map, hp, hq]


set_option backward.isDefEq.respectTransparency false in
/-- The actual terminal guard syntax commutes with arbitrary atom maps. -/
theorem terminal_map {A B : Type} (f : A → B) (p : NNF.Formula A)
    (X : State (shape p)) :
    terminal (p.map f) (mapState f p X) = (terminal p X).map f := by
  induction p with
  | pos a => cases h : bit X <;> simp [NNF.Formula.map, terminal, h, Guard.map]
  | neg a => cases h : bit X <;> simp [NNF.Formula.map, terminal, h, Guard.map]
  | bot => simp [NNF.Formula.map, terminal]
  | top => simp [NNF.Formula.map, terminal]
  | strongNext p hp | weakNext p hp => simp [NNF.Formula.map, terminal, Guard.map, hp]
  | conj p q hp hq | disj p q hp hq | «until» p q hp hq | release p q hp hq =>
      simp [NNF.Formula.map, terminal, Guard.map, hp, hq]

/-- Language pullback agrees even when a renaming identifies leaves. -/
theorem accepts_map {A B : Type} (f : A → B) (p : NNF.Formula A)
    (n : Nat) (word : Nat → B → Prop) :
    Accepts (p.map f) n word ↔ Accepts p n (fun t a => word t (f a)) := by
  rw [accepts_iff, accepts_iff]
  exact p.holds_map f (some n) word 0

end Silmaril.Logic.Temporal.CTLStar.FiniteTableau
