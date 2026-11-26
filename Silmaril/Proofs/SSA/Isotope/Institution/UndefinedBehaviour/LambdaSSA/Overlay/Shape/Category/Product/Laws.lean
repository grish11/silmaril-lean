module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Product.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Behaviour

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.Product

open CategoryTheory
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category (return_bind)

universe v w x

variable {α : Type w} {σ : Type x} {κ : Type v} {atomType : α → κ → Prop} {A B C : Ty κ}

theorem pair_split (p : singlePayload (atomType := atomType) (.product A B)) :
    pairPayload (splitPair p).1 (splitPair p).2 = p := by
  obtain ⟨_, typed⟩ := p
  cases typed
  rfl

theorem value_comp (f : singlePayload (atomType := atomType) A → singlePayload (atomType := atomType) B)
    (g : singlePayload (atomType := atomType) B → singlePayload (atomType := atomType) C) :
    valueArrow (σ := σ) f ≫ valueArrow g = valueArrow (g ∘ f) := by
  apply arrow_ext
  intro i a s
  have hi := Fin.eq_zero i
  subst i
  exact (return_bind 0 (f a).val s _).trans ((valueArrow g).total_typed 0 (f a) s)

theorem whiskerLeft_value (X : Ty κ)
    (f : singlePayload (atomType := atomType) A → singlePayload (atomType := atomType) B) :
    whiskerLeft X (valueArrow (σ := σ) f) =
      valueArrow (fun p => pairPayload (splitPair p).1 (f (splitPair p).2)) := by
  apply arrow_ext
  intro i a s
  have hi := Fin.eq_zero i
  subst i
  exact return_bind 0 (f (splitPair a).2).val s _

theorem whiskerRight_value (X : Ty κ)
    (f : singlePayload (atomType := atomType) A → singlePayload (atomType := atomType) B) :
    whiskerRight (valueArrow (σ := σ) f) X =
      valueArrow (fun p => pairPayload (f (splitPair p).1) (splitPair p).2) := by
  apply arrow_ext
  intro i a s
  have hi := Fin.eq_zero i
  subst i
  exact return_bind 0 (f (splitPair a).1).val s _

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.Product
