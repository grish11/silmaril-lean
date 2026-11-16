module

public import Silmaril.Logic.Institution.Syntactic.Defs

@[expose] public section

namespace Silmaril.Logic.Institution.Syntactic

open Silmaril.Logic.Institution.Metatheory

universe w

/-- Every supplied hypothesis belongs to its generated theory. -/
theorem subset_generated (S : ER.{w}) (Γ : Set S.Sen) : Γ ⊆ (generated S Γ).sentences :=
  fun φ hφ => S.mono (Set.singleton_subset_iff.mpr hφ) (S.refl φ)

/-- Generated theories are the least closed theories containing their hypotheses. -/
theorem generated_le_iff (S : ER.{w}) (Γ : Set S.Sen) (T : Theory S) :
    (generated S Γ).sentences ⊆ T.sentences ↔ Γ ⊆ T.sentences := by
  constructor
  · exact fun h => (subset_generated S Γ).trans h
  · exact fun h φ hd => T.closed φ (S.mono h hd)

/-- Closed-theory semantics is sound and complete for the supplied entailment relation. -/
theorem derives_iff_entails (S : ER.{w}) (Γ : Set S.Sen) (φ : S.Sen) :
    S.Derives Γ φ ↔ (room S).Entails Γ φ := by
  constructor
  · intro h M hM
    exact M.as.closed φ (S.mono hM h)
  · intro h
    exact h (CategoryTheory.Discrete.mk (generated S Γ))
      (subset_generated S Γ)

end Silmaril.Logic.Institution.Syntactic
