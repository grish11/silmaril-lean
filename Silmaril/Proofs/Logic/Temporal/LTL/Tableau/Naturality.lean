module

public import Silmaril.Proofs.Logic.Temporal.LTL.Tableau.Language

@[expose] public section
noncomputable section
open Classical
namespace Silmaril.Logic.Temporal.LTL.Tableau
open Buchi.Automaton

def castState {s t : Shape} (h : s = t) (X : State s) : State t := h ▸ X
def castOcc {s t : Shape} (h : s = t) (i : Occ s) : Occ t := h ▸ i

theorem castState_bit {s t : Shape} (h : s = t) (X : State s) :
    bit (castState h X) = bit X := by cases h; rfl

theorem castState_unary {s t : Shape} (h : s = t) (X : State (.unary s)) :
    unary (castState (congrArg Shape.unary h) X) = castState h (unary X) := by cases h; rfl

theorem castState_left {s t u v : Shape} (h : s = t) (j : u = v) (X : State (.binary s u)) :
    left (castState (congrArg₂ Shape.binary h j) X) = castState h (left X) := by cases h; cases j; rfl

theorem castState_right {s t u v : Shape} (h : s = t) (j : u = v) (X : State (.binary s u)) :
    right (castState (congrArg₂ Shape.binary h j) X) = castState j (right X) := by cases h; cases j; rfl

def mapState {Atom Atom' : Type} (f : Atom → Atom') (p : NNF.Formula Atom)
    (X : State (shape p)) : State (shape (p.map f)) := castState (shape_map f p).symm X

@[simp] theorem mapState_bit {Atom Atom' : Type} (f : Atom → Atom') (p : NNF.Formula Atom)
    (X : State (shape p)) : bit (mapState f p X) = bit X := castState_bit _ _

@[simp] theorem mapState_unary {Atom Atom' : Type} (f : Atom → Atom') (p : NNF.Formula Atom)
    (X : State (shape (.next p))) : unary (mapState f (.next p) X) = mapState f p (unary X) :=
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
  | next p hp => simp [NNF.Formula.map, transition, Guard.map, hp]
  | conj p q hp hq => simp [NNF.Formula.map, transition, Guard.map, hp, hq]
  | disj p q hp hq => simp [NNF.Formula.map, transition, Guard.map, hp, hq]
  | «until» p q hp hq => simp [NNF.Formula.map, transition, Guard.map, hp, hq]
  | release p q hp hq => simp [NNF.Formula.map, transition, Guard.map, hp, hq]

def mapOcc {Atom Atom' : Type} (f : Atom → Atom') (p : NNF.Formula Atom)
    (i : Occ (shape p)) : Occ (shape (p.map f)) := castOcc (shape_map f p).symm i

theorem castOcc_unary {s t : Shape} (h : s = t) (i : Occ (.unary s)) :
    castOcc (congrArg Shape.unary h) i =
      match i with
      | .inl u => .inl u
      | .inr j => .inr (castOcc h j) := by cases h; cases i <;> rfl

theorem castOcc_binary {s t u v : Shape} (h : s = t) (j : u = v)
    (i : Occ (.binary s u)) :
    castOcc (congrArg₂ Shape.binary h j) i =
      match i with
      | .inl w => .inl w
      | .inr (.inl k) => .inr (.inl (castOcc h k))
      | .inr (.inr k) => .inr (.inr (castOcc j k)) := by
  cases h; cases j; cases i with
  | inl _ => rfl
  | inr k => cases k <;> rfl

set_option backward.isDefEq.respectTransparency false in
theorem discharged_map {Atom Atom' : Type} (f : Atom → Atom') (p : NNF.Formula Atom)
    (X : State (shape p)) (i : Occ (shape p)) :
    discharged (p.map f) (mapState f p X) (mapOcc f p i) = discharged p X i := by
  induction p with
  | pos a => rfl
  | neg a => rfl
  | bot => rfl
  | top => rfl
  | next p hp =>
    have hi := castOcc_unary (shape_map f p).symm i
    change mapOcc f (.next p) i = _ at hi
    rw [hi]
    cases i with
    | inl u => rfl
    | inr j => simpa only [NNF.Formula.map, discharged, mapState_unary, mapOcc] using hp (unary X) _
  | conj p q hp hq | disj p q hp hq | «until» p q hp hq | release p q hp hq =>
    show discharged _ _ _ = discharged _ _ _
    have hi := castOcc_binary (shape_map f p).symm (shape_map f q).symm i
    change mapOcc f _ i = _ at hi
    rw [hi]
    cases i with
    | inl u => simp [NNF.Formula.map, discharged]
    | inr k => cases k with
      | inl j => simpa only [NNF.Formula.map, discharged, mapState_conj_left,
          mapState_disj_left, mapState_until_left, mapState_release_left, mapOcc] using hp (left X) j
      | inr j => simpa only [NNF.Formula.map, discharged, mapState_conj_right,
          mapState_disj_right, mapState_until_right, mapState_release_right, mapOcc] using hq (right X) j

theorem pack_map {Atom Atom' : Type} (f : Atom → Atom') (s : Shape)
    (edge : State s → State s → Guard Atom) (accept : State s → Occ s → Prop) :
    pack s (fun X Y => (edge X Y).map f) accept = (pack s edge accept).map f := rfl

theorem pack_transport {Atom : Type} {s t : Shape} (h : s = t)
    (edge : State s → State s → Guard Atom) (accept : State s → Occ s → Prop)
    (edge' : State t → State t → Guard Atom) (accept' : State t → Occ t → Prop)
    (he : ∀ X Y, edge' (castState h X) (castState h Y) = edge X Y)
    (ha : ∀ X i, accept' (castState h X) (castOcc h i) = accept X i) :
    HEq (pack t edge' accept') (pack s edge accept) := by
  cases h
  have he' : edge' = edge := funext fun X => funext fun Y => he X Y
  have ha' : accept' = accept := funext fun X => funext fun i => ha X i
  cases he'; cases ha'; rfl

/-- Exact syntax equality after transport along atom-independent erased shape. -/
theorem automaton_map {Atom Atom' : Type} (f : Atom → Atom') (p : NNF.Formula Atom) :
    HEq (automaton (p.map f)) ((automaton p).map f) := by
  rw [automaton, automaton, ← pack_map]
  exact pack_transport (shape_map f p).symm _ _ _ _
    (transition_map f p) (discharged_map f p)

end Silmaril.Logic.Temporal.LTL.Tableau
