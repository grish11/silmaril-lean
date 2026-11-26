module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Behaviour

/-! # Exact sum and empty types in the shaped observation category -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category

open CategoryTheory

universe v w x

variable {α : Type w} {σ : Type x} {κ : Type v} {atomType : α → κ → Prop}

/-- The interface with one label of the given exact type. -/
abbrev single (A : Ty κ) : Interface α σ atomType := ⟨[A]⟩

variable {A B : Ty κ} {Z : Interface α σ atomType}

abbrev singlePayload (A : Ty κ) := {a : Value α // ValueTyped atomType a A}

abbrev payloadAtZero {i : Fin 1} (a : (single (σ := σ) (atomType := atomType) A).Payload i) :
    singlePayload (atomType := atomType) A :=
  ⟨a.val, (Fin.eq_zero i) ▸ a.property⟩

/-- A shaped sum payload carries exactly one of the two typed alternatives. -/
def splitPayload (a : singlePayload (atomType := atomType) (.coprod A B)) :
    singlePayload (atomType := atomType) A ⊕ singlePayload (atomType := atomType) B :=
  match a with
  | ⟨.inl b, typed⟩ => .inl ⟨b, by cases typed; assumption⟩
  | ⟨.inr b, typed⟩ => .inr ⟨b, by cases typed; assumption⟩
  | ⟨.unit, typed⟩ | ⟨.atom _, typed⟩ | ⟨.pair _ _, typed⟩ => False.elim (by cases typed)

open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category (ordinary_return_iff) in
/-- The left injection returns a tag without changing the state. -/
def sumInl (A B : Ty κ) : single A ⟶ (single (.coprod A B) : Interface α σ atomType) where
  run _ a s := ↑({Outcome.ret 0 (.inl a.val) s} : Set (Outcome 1 α σ))
  returnsTyped _ a _ := by
    intro _ _ _ reached
    obtain ⟨rfl, rfl, rfl⟩ := Outcome.ret.inj (ordinary_return_iff.mp reached)
    exact .inl (payloadAtZero a).property

open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category (ordinary_return_iff) in
/-- The right injection returns a tag without changing the state. -/
def sumInr (A B : Ty κ) : single B ⟶ (single (.coprod A B) : Interface α σ atomType) where
  run _ a s := ↑({Outcome.ret 0 (.inr a.val) s} : Set (Outcome 1 α σ))
  returnsTyped _ a _ := by
    intro _ _ _ reached
    obtain ⟨rfl, rfl, rfl⟩ := Outcome.ret.inj (ordinary_return_iff.mp reached)
    exact .inr (payloadAtZero a).property

/-- Dispatch to the selected arrow at the incoming state. The selected
behaviour is returned in full, including faults, divergence and fresh top. -/
def sumDesc (f : single A ⟶ Z) (g : single B ⟶ Z) : single (.coprod A B) ⟶ Z where
  run _ a s := (splitPayload (payloadAtZero a)).elim (fun x => f.run 0 x s) (fun y => g.run 0 y s)
  returnsTyped _ a s := by
    cases splitPayload (payloadAtZero a) with
    | inl b => exact f.returnsTyped 0 b s
    | inr b => exact g.returnsTyped 0 b s

theorem noEmptyPayload (a : singlePayload (atomType := atomType) (.empty : Ty κ)) : False := by
  obtain ⟨_, typed⟩ := a
  cases typed

/-- An empty-typed input has no runtime payload in a shaped model. -/
def emptyElim (Z : Interface α σ atomType) : single .empty ⟶ Z where
  run _ a _ := False.elim (noEmptyPayload (payloadAtZero a))
  returnsTyped _ a _ := False.elim (noEmptyPayload (payloadAtZero a))

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category
