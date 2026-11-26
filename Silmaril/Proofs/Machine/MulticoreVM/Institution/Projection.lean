module

public import Silmaril.Machine.MulticoreVM.Institution.Projection.Defs

public section

namespace Silmaril.Proofs.Machine.MulticoreVM.Institution

open CategoryTheory
open Silmaril.Machine.MulticoreVM
open Silmaril.Machine.MulticoreVM.Institution
open Silmaril.Semantics.ConcurrentTrace (Word)

universe u

variable {F G : Sig.{u} ⥤ Type u} (π : F ⟶ G) {A B : Sig.{u}} (f : A ⟶ B)

theorem sentence_natural (φ : Sentence (F.obj A)) :
    (φ.map (F.map f)).map (π.app B) = (φ.map (π.app A)).map (G.map f) := by
  rw [← sentenceMap_comp, ← sentenceMap_comp]
  exact congrArg (fun k => φ.map k) (funext (π.naturality_apply f))

theorem reduct_natural (M : Model (G.obj B)) :
    reduct (F.map f) (reduct (π.app B) M) = reduct (π.app A) (reduct (G.map f) M) := by
  ext obs
  change π.app B (F.map f obs) ∈ M ↔ G.map f (π.app A obs) ∈ M
  rw [π.naturality_apply f]

theorem image_natural (M : Model (F.obj A)) :
    (π.app B) '' ((F.map f) '' M) = (G.map f) '' ((π.app A) '' M) := by
  rw [Set.image_image, Set.image_image]
  exact congrArg (fun k => k '' M) (funext (π.naturality_apply f))

theorem image_reduct_subset (M : Model (F.obj B)) :
    (π.app A) '' reduct (F.map f) M ⊆ reduct (G.map f) ((π.app B) '' M) := by
  rintro _ ⟨obs, hobs, rfl⟩
  exact ⟨F.map f obs, hobs, π.naturality_apply f obs⟩

theorem image_reduct_eq_iff :
    (∀ M : Model (F.obj B),
      (π.app A) '' reduct (F.map f) M = reduct (G.map f) ((π.app B) '' M)) ↔
      ∀ (a : G.obj A) (b : F.obj B), π.app B b = G.map f a →
        ∃ x : F.obj A, π.app A x = a ∧ F.map f x = b := by
  constructor
  · intro commutes a b compatible
    have h : a ∈ reduct (G.map f) ((π.app B) '' ({b} : Set (F.obj B))) :=
      ⟨b, rfl, compatible⟩
    rw [← commutes] at h
    obtain ⟨x, hx, ha⟩ := h
    exact ⟨x, ha, Set.mem_singleton_iff.mp hx⟩
  · intro lift M
    refine Set.Subset.antisymm (image_reduct_subset π f M) ?_
    intro a ha
    obtain ⟨b, hb, compatible⟩ := ha
    obtain ⟨x, rfl, hxb⟩ := lift a b compatible
    refine ⟨x, ?_, rfl⟩
    change F.map f x ∈ M
    rwa [hxb]

theorem image_ofVM {State Thread Choice Event O P : Type u}
    (project : O → P) (observe : Word Thread Event → O)
    (step : Transition State Thread Choice Event) (initial : State) :
    project '' ofVM observe step initial = ofVM (project ∘ observe) step initial := by
  ext obs
  constructor
  · rintro ⟨_, ⟨schedule, word, final, run, rfl⟩, rfl⟩
    exact ⟨schedule, word, final, run, rfl⟩
  · rintro ⟨schedule, word, final, run, rfl⟩
    exact ⟨observe word, ⟨schedule, word, final, run, rfl⟩, rfl⟩

end Silmaril.Proofs.Machine.MulticoreVM.Institution
