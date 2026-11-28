module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.ExactSum.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Laws

/-! # Typed product values and fixed-factor computations -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category

open CategoryTheory

universe v w x

variable {α : Type w} {σ : Type x} {κ : Type v} {atomType : α → κ → Prop} {A B C X : Ty κ}

def pairPayload (a : singlePayload (atomType := atomType) A) (b : singlePayload (atomType := atomType) B) :
    singlePayload (atomType := atomType) (.product A B) :=
  ⟨.pair a.val b.val, .pair a.property b.property⟩

def splitPair (p : singlePayload (atomType := atomType) (.product A B)) :
    singlePayload (atomType := atomType) A × singlePayload (atomType := atomType) B :=
  match p with
  | ⟨.pair a b, typed⟩ => (⟨a, by cases typed; assumption⟩, ⟨b, by cases typed; assumption⟩)
  | ⟨.unit, typed⟩ | ⟨.atom _, typed⟩ | ⟨.inl _, typed⟩ | ⟨.inr _, typed⟩ =>
    False.elim (by cases typed)

/-- The deterministic, state-preserving inclusion of a typed value map. -/
def valueArrow (f : singlePayload (atomType := atomType) A → singlePayload (atomType := atomType) B) :
    single A ⟶ (single B : Interface α σ atomType) where
  run _ a s := ↑({Outcome.ret 0 (f (payloadAtZero a)).val s} : Set (Outcome 1 α σ))
  returnsTyped _ a _ := by
    intro _ _ _ reached
    obtain ⟨rfl, rfl, rfl⟩ := Outcome.ret.inj
      (Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.ordinary_return_iff.mp reached)
    exact (f (payloadAtZero a)).property

/-- Build an ordinary result with its original final state. -/
abbrev returnPayload (a : Value α) (s : σ) : Behaviour 1 α σ :=
  ↑({Outcome.ret 0 a s} : Set (Outcome 1 α σ))

/-- Run the active component and repack successful returns, keeping their final
states. Fault, may-divergence and fresh top propagate through the bind. -/
noncomputable def repackage (p : Behaviour 1 α σ) (pack : Value α → Value α) : Behaviour 1 α σ :=
  p.bind fun _ b s => returnPayload (pack b) s

theorem repackage_typed {p : Behaviour 1 α σ} (shaped : ReturnsTyped atomType (L := [B]) p)
    (pack : Value α → Value α) (typed : ∀ b, ValueTyped atomType b B → ValueTyped atomType (pack b) C) :
    ReturnsTyped atomType (L := [C]) (repackage p pack) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.repackage_typed shaped pack typed

noncomputable def whiskerLeft (X : Ty κ) (f : single A ⟶ (single B : Interface α σ atomType)) :
    single (.product X A) ⟶ (single (.product X B) : Interface α σ atomType) where
  run _ a s :=
    let (left, right) := splitPair (payloadAtZero a)
    repackage (f.run 0 right s) (.pair left.val)
  returnsTyped _ a s := by
    obtain ⟨left, right⟩ := splitPair (payloadAtZero a)
    exact repackage_typed (f.returnsTyped 0 right s) _ (fun _ h => .pair left.property h)

noncomputable def whiskerRight (f : single A ⟶ (single B : Interface α σ atomType)) (X : Ty κ) :
    single (.product A X) ⟶ (single (.product B X) : Interface α σ atomType) where
  run _ a s :=
    let (left, right) := splitPair (payloadAtZero a)
    repackage (f.run 0 left s) (fun b => .pair b right.val)
  returnsTyped _ a s := by
    obtain ⟨left, right⟩ := splitPair (payloadAtZero a)
    exact repackage_typed (f.returnsTyped 0 left s) _ (fun _ h => .pair h right.property)

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category
