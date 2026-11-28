module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Defs
import Mathlib.Data.Set.Lattice.Image

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.Iteration

open Silmaril Silmaril.Isotope CategoryTheory
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category

universe v w x

variable {α : Type w} {σ : Type x} {κ : Type v} {atomType : α → κ → Prop} {A B : Ty κ}

theorem iterateObservations_mono
    {f g : single A ⟶ (single (.coprod B A) : Interface α σ atomType)}
    (le : ∀ (a : singlePayload (atomType := atomType) A) (s : σ), f.run (0 : Fin 1) a s ≤ g.run (0 : Fin 1) a s)
    (a : singlePayload (atomType := atomType) A) (s : σ) :
    iterateObservations f a s ≤ iterateObservations g a s := by
  apply Feedback.close_mono
  intro p
  cases p with
  | entry => exact le_rfl
  | block i b t =>
    apply WithTop.monotone_map_iff.mpr Set.monotone_preimage
    change f.total (0 : Fin 1) b t ≤ g.total (0 : Fin 1) b t
    unfold Arrow.total
    split
    · rename_i typed
      exact le ⟨b, typed⟩ t
    · exact le_rfl

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.Iteration
