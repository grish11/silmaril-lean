module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Monotonicity

/-! # Refinement of repeated exact-sum observations -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category

open CategoryTheory

universe v w x

variable {α : Type w} {σ : Type x} {κ : Type v} {atomType : α → κ → Prop} {A B : Ty κ}

/-- Pointwise refinement of the typed step suffices for ordered iteration.
Successors include the exact reply payload and final machine state. -/
theorem iterateObservations_mono
    {f g : single A ⟶ (single (.coprod B A) : Interface α σ atomType)}
    (le : ∀ (a : singlePayload (atomType := atomType) A) (s : σ), f.run (0 : Fin 1) a s ≤ g.run (0 : Fin 1) a s)
    (a : singlePayload (atomType := atomType) A) (s : σ) :
    iterateObservations f a s ≤ iterateObservations g a s :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.Iteration.iterateObservations_mono le a s

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category
