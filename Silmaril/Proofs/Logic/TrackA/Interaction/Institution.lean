module

public import Silmaril.Logic.TrackA.Interaction.Defs

public section

namespace Silmaril.Proofs.Logic.TrackA.Interaction

open CategoryTheory Opposite Silmaril.Logic.Institution Silmaril.Logic.TrackA.Interaction

universe u v w m

variable {C : Type u} [Category.{v} C] (system : RefinementSystem.{u,v,w,m} C)

private theorem discrete_functor_ext {D E : Type*} {F G : Discrete D ⥤ Discrete E}
    (objects : ∀ x, F.obj x = G.obj x) : F = G :=
  CategoryTheory.Functor.ext objects (fun _ _ _ => Subsingleton.elim _ _)

theorem corridor_id (S : Cᵒᵖ) : system.corridor (𝟙 S) = 𝟙 (system.room S) := by
  apply Corridor.ext
  · funext bound
    change system.Observation.map (𝟙 S.unop) ⁻¹' bound = bound
    rw [CategoryTheory.Functor.map_id]
    rfl
  · apply discrete_functor_ext (D := system.Model.obj _) (E := system.Model.obj _)
    intro model
    change Discrete.mk (system.Model.map (𝟙 S.unop) model.as) = model
    rw [CategoryTheory.Functor.map_id]
    cases model
    rfl

theorem corridor_comp {S T U : Cᵒᵖ} (f : S ⟶ T) (g : T ⟶ U) :
    system.corridor (f ≫ g) = system.corridor f ≫ system.corridor g := by
  apply Corridor.ext
  · funext bound
    change system.Observation.map (g.unop ≫ f.unop) ⁻¹' bound =
      system.Observation.map g.unop ⁻¹' (system.Observation.map f.unop ⁻¹' bound)
    rw [CategoryTheory.Functor.map_comp]
    rfl
  · apply discrete_functor_ext (D := system.Model.obj _) (E := system.Model.obj _)
    intro model
    change Discrete.mk (system.Model.map (g.unop ≫ f.unop) model.as) =
      Discrete.mk (system.Model.map f.unop (system.Model.map g.unop model.as))
    rw [CategoryTheory.Functor.map_comp]
    rfl


section Catastrophic

open Silmaril.Semantics.TrackA.Interaction

variable {A : Type w} {S T U : TraceSignature.{u,v}}

private theorem translate_id (bound : UB.Catastrophic (Trace S.signature A)) :
    catastrophicTranslate (𝟙 S) bound = bound := by
  apply Subtype.ext
  change (explicitObservations A).map (𝟙 S) ⁻¹' bound.val = bound.val
  rw [CategoryTheory.Functor.map_id]
  rfl

private theorem translate_comp (f : S ⟶ T) (g : T ⟶ U)
    (bound : UB.Catastrophic (Trace U.signature A)) :
    catastrophicTranslate (f ≫ g) bound = catastrophicTranslate f (catastrophicTranslate g bound) := by
  apply Subtype.ext
  change (explicitObservations A).map (f ≫ g) ⁻¹' bound.val =
    (explicitObservations A).map f ⁻¹' ((explicitObservations A).map g ⁻¹' bound.val)
  rw [CategoryTheory.Functor.map_comp]
  rfl

theorem catastrophic_corridor_id (A : Type w) (S : TraceSignature.{u,v}ᵒᵖ) :
    catastrophicCorridor A (𝟙 S) = 𝟙 (catastrophicRoom A S) := by
  apply Corridor.ext
  · exact funext translate_id
  · apply discrete_functor_ext (D := UB.Catastrophic (Trace S.unop.signature A))
      (E := UB.Catastrophic (Trace S.unop.signature A))
    rintro ⟨model⟩
    exact congrArg Discrete.mk
      ((catastrophic_gc (A := A) (𝟙 S.unop)).l_unique GaloisConnection.id translate_id)

theorem catastrophic_corridor_comp (A : Type w) {S T U : TraceSignature.{u,v}ᵒᵖ}
    (f : S ⟶ T) (g : T ⟶ U) :
    catastrophicCorridor A (f ≫ g) = catastrophicCorridor A f ≫ catastrophicCorridor A g := by
  apply Corridor.ext
  · exact funext (translate_comp g.unop f.unop)
  · apply discrete_functor_ext (D := UB.Catastrophic (Trace U.unop.signature A))
      (E := UB.Catastrophic (Trace S.unop.signature A))
    intro model
    exact congrArg Discrete.mk ((catastrophic_gc (A := A) (g.unop ≫ f.unop)).l_unique
      ((catastrophic_gc g.unop).compose (catastrophic_gc f.unop)) (translate_comp g.unop f.unop))

theorem catastrophic_reduct_collapse (f : S ⟶ T) (runs : UB.Explicit (Trace S.signature A)) :
    catastrophicReduct f (UB.collapse runs) = UB.collapse ((explicitObservations A).map f '' runs) := by
  have compare (bound : UB.Catastrophic (Trace T.signature A)) :
      catastrophicReduct f (UB.collapse runs) ≤ bound ↔
        UB.collapse ((explicitObservations A).map f '' runs) ≤ bound :=
    (catastrophic_gc f _ _).trans ((UB.collapse_gc _ _ _).trans
      (Set.image_subset_iff.symm.trans (UB.collapse_gc _ _ _).symm))
  exact le_antisymm ((compare _).mpr le_rfl) ((compare _).mp le_rfl)

end Catastrophic

end Silmaril.Proofs.Logic.TrackA.Interaction
