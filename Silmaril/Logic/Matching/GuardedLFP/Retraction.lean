module

public import Mathlib.Order.FixedPoints
public import Mathlib.Data.Set.Image

@[expose] public section
namespace Silmaril.Logic.Matching.GuardedLFP

/-- Encode valid values in a larger raw carrier; no surjectivity is required. -/
def encode {A B : Type} (e : A → B) : Set A →o Set B where
  toFun X := e '' X
  monotone' := fun _ _ h => Set.image_mono h

def restrict {A B : Type} (e : A → B) : Set B →o Set A where
  toFun X := e ⁻¹' X
  monotone' := fun _ _ h => Set.preimage_mono h

theorem restrict_encode {A B : Type} (e : A → B) (he : Function.Injective e) (X : Set A) :
    restrict e (encode e X) = X := by
  apply Set.ext
  intro x
  constructor
  · rintro ⟨y, hy, h⟩
    exact he h ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- Retraction, rather than a false equivalence of the full padded powerset,
transports least fixed points even for arbitrary raw candidate sets. -/
theorem lfp_retraction {A B : Type} (e : A → B) (he : Function.Injective e)
    (F : Set A →o Set A) (G : Set B →o Set B)
    (compatible : ∀ X, G X = encode e (F (restrict e X))) :
    G.lfp = encode e F.lfp := by
  have fixed : G (encode e F.lfp) = encode e F.lfp := by
    rw [compatible, restrict_encode e he, F.map_lfp]
  have upper : G.lfp ⊆ encode e F.lfp := G.lfp_le fixed.le
  have unfolded : G.lfp = encode e (F (restrict e G.lfp)) :=
    G.map_lfp.symm.trans (compatible G.lfp)
  have source_prefixed : F (restrict e G.lfp) ⊆ restrict e G.lfp := by
    intro a ha
    change e a ∈ G.lfp
    rw [unfolded]
    exact ⟨a, ha, rfl⟩
  have lower : encode e F.lfp ⊆ G.lfp := by
    rintro _ ⟨a, ha, rfl⟩
    exact F.lfp_le source_prefixed ha
  exact Set.Subset.antisymm upper lower
end Silmaril.Logic.Matching.GuardedLFP
