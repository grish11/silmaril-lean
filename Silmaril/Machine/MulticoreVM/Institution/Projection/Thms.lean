module

public import Silmaril.Machine.MulticoreVM.Institution.Projection.Defs
import Silmaril.Proofs.Machine.MulticoreVM.Institution.Projection

public section

namespace Silmaril.Machine.MulticoreVM.Institution

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Semantics.ConcurrentTrace (Word)

universe u

/-- The identity projection induces the identity of the room functor. -/
@[simp] theorem roomProjection_id (F : Sig.{u} ⥤ Type u) :
    roomProjection (𝟙 F) = 𝟙 (F ⋙ observationInstitution) :=
  ((Functor.whiskeringRight _ _ _).obj observationInstitution).map_id F

/-- Composing projections composes their natural transformations of rooms. -/
theorem roomProjection_comp {F G H : Sig.{u} ⥤ Type u} (π : F ⟶ G) (ρ : G ⟶ H) :
    roomProjection (π ≫ ρ) = roomProjection π ≫ roomProjection ρ :=
  ((Functor.whiskeringRight _ _ _).obj observationInstitution).map_comp π ρ

variable {F G : Sig.{u} ⥤ Type u} (π : F ⟶ G) {A B : Sig.{u}} (f : A ⟶ B)

/-- Sentence translation around a natural observation square agrees on both paths. -/
theorem sentence_natural (φ : Sentence (F.obj A)) :
    (φ.map (F.map f)).map (π.app B) = (φ.map (π.app A)).map (G.map f) :=
  Proofs.Machine.MulticoreVM.Institution.sentence_natural π f φ

/-- The two composites of inverse-image reducts around a natural observation square agree. -/
theorem reduct_natural (M : Model (G.obj B)) :
    reduct (F.map f) (reduct (π.app B) M) = reduct (π.app A) (reduct (G.map f) M) :=
  Proofs.Machine.MulticoreVM.Institution.reduct_natural π f M

/-- Direct-image observation commutes with forward renaming of a behavior set. -/
theorem image_natural (M : Model (F.obj A)) :
    (π.app B) '' ((F.map f) '' M) = (G.map f) '' ((π.app A) '' M) :=
  Proofs.Machine.MulticoreVM.Institution.image_natural π f M

/-- Projecting after taking a reduct gives a subset of the reduct of the projected behavior. -/
theorem image_reduct_subset (M : Model (F.obj B)) :
    (π.app A) '' reduct (F.map f) M ⊆ reduct (G.map f) ((π.app B) '' M) :=
  Proofs.Machine.MulticoreVM.Institution.image_reduct_subset π f M

/-- The mixed direct-image and inverse-image square commutes for all models exactly when
every compatible pair has a lift. This is the witness condition for a weak pullback in types. -/
theorem image_reduct_eq_iff :
    (∀ M : Model (F.obj B),
      (π.app A) '' reduct (F.map f) M = reduct (G.map f) ((π.app B) '' M)) ↔
      ∀ (a : G.obj A) (b : F.obj B), π.app B b = G.map f a →
        ∃ x : F.obj A, π.app A x = a ∧ F.map f x = b :=
  Proofs.Machine.MulticoreVM.Institution.image_reduct_eq_iff π f

/-- Observing the same successful VM schedules through a composite is a direct image. -/
theorem image_ofVM {State Thread Choice Event O P : Type u}
    (project : O → P) (observe : Word Thread Event → O)
    (step : Transition State Thread Choice Event) (initial : State) :
    project '' ofVM observe step initial = ofVM (project ∘ observe) step initial :=
  Proofs.Machine.MulticoreVM.Institution.image_ofVM project observe step initial

/-- A natural projection can be applied before or after forward renaming of VM observations. -/
theorem ofVM_natural {State Thread Choice Event : Type u} (observe : Word Thread Event → F.obj A)
    (step : Transition State Thread Choice Event) (initial : State) :
    ofVM ((π.app B) ∘ (F.map f) ∘ observe) step initial =
      (G.map f) '' ofVM ((π.app A) ∘ observe) step initial := by
  rw [← image_ofVM, ← image_ofVM, image_natural π f, image_ofVM]

end Silmaril.Machine.MulticoreVM.Institution
