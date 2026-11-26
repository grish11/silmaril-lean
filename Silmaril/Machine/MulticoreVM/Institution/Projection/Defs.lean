module

public import Silmaril.Machine.MulticoreVM.Institution.Thms
public import Mathlib.CategoryTheory.Whiskering
import Silmaril.Semantics.ConcurrentTrace.Thms

/-! # Natural projections between VM observation profiles -/

@[expose] public section

namespace Silmaril.Machine.MulticoreVM.Institution

open CategoryTheory Silmaril.Logic.Institution

universe u

variable {F G : Sig.{u} ⥤ Type u}

/-- A natural projection induces a natural transformation of room functors. Each component
translates sentences along the projection and reduces models by inverse image. -/
def roomProjection (π : F ⟶ G) :
    F ⋙ observationInstitution ⟶ G ⋙ observationInstitution :=
  Functor.whiskerRight π observationInstitution

/-- The quotient map is a natural projection from chronological thread words. -/
def namedToConcurrent : namedWords.{u} ⟶ concurrentTraces.{u} where
  app _ := TypeCat.ofHom Semantics.ConcurrentTrace.ofWord
  naturality {A B} f := by
    apply TypeCat.homEquiv.injective
    funext word
    exact (Semantics.ConcurrentTrace.mapTrace_ofWord f.thread f.thread.injective f.event word).symm

end Silmaril.Machine.MulticoreVM.Institution
