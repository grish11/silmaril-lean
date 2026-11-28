module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Product.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Product.Laws

/-! # Cartesian pairing of shaped value maps -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category

open CategoryTheory

universe v w x

variable {α : Type w} {σ : Type x} {κ : Type v} {atomType : α → κ → Prop} {A B C X : Ty κ}

@[simp] theorem split_pair (a : singlePayload (atomType := atomType) A)
    (b : singlePayload (atomType := atomType) B) : splitPair (pairPayload a b) = (a, b) :=
  rfl

@[simp] theorem pair_split (p : singlePayload (atomType := atomType) (.product A B)) :
    pairPayload (splitPair p).1 (splitPair p).2 = p :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.Product.pair_split p

/-- The two components determine a value map into the exact product. -/
theorem value_pair_unique {f g : singlePayload (atomType := atomType) X →
    singlePayload (atomType := atomType) (.product A B)}
    (hl : ∀ x, (splitPair (f x)).1 = (splitPair (g x)).1)
    (hr : ∀ x, (splitPair (f x)).2 = (splitPair (g x)).2) : f = g :=
  funext fun x => (pair_split (f x)).symm.trans ((congrArg₂ pairPayload (hl x) (hr x)).trans (pair_split (g x)))

@[simp] theorem value_comp (f : singlePayload (atomType := atomType) A → singlePayload (atomType := atomType) B)
    (g : singlePayload (atomType := atomType) B → singlePayload (atomType := atomType) C) :
    valueArrow (σ := σ) f ≫ valueArrow g = valueArrow (g ∘ f) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.Product.value_comp f g

theorem whiskerLeft_value (X : Ty κ)
    (f : singlePayload (atomType := atomType) A → singlePayload (atomType := atomType) B) :
    whiskerLeft X (valueArrow (σ := σ) f) =
      valueArrow (fun p => pairPayload (splitPair p).1 (f (splitPair p).2)) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.Product.whiskerLeft_value X f

theorem whiskerRight_value (X : Ty κ)
    (f : singlePayload (atomType := atomType) A → singlePayload (atomType := atomType) B) :
    whiskerRight (valueArrow (σ := σ) f) X =
      valueArrow (fun p => pairPayload (f (splitPair p).1) (splitPair p).2) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.Product.whiskerRight_value X f

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category
