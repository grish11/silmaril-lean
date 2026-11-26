module

public import Silmaril.ProofFormats.LeanNDJSON.MLTT.Signature.Defs

@[expose] public section

namespace Silmaril.Proofs.ProofFormats.LeanNDJSON.MLTT

open CategoryTheory Silmaril.ProofFormats.LeanNDJSON.MLTT

variable {Name : Type} {S T : Signature Name}

theorem derives_cut {H K : Set (Sentence S)} {s : Sentence S}
    (hK : ∀ k ∈ K, Derives H k) (h : Derives (H ∪ K) s) : Derives H s := by
  apply h.bind
  rintro _ ⟨k, hk, rfl⟩
  rcases hk with hk | hk
  · exact .hyp ⟨k, hk, rfl⟩
  · exact hK k hk

theorem derives_weaken (f : S ⟶ T) (H : Set (Sentence S)) (s : Sentence S) :
    Derives H s ↔ Derives (Sentence.weaken f '' H) (s.weaken f) := by
  unfold Derives
  rw [Set.image_image]
  rfl

theorem resolve?_weaken [DecidableEq Name] {name : Name}
    {i : Fin S.declarations.length} (f : S ⟶ T) (h : S.resolve? name = some i) :
    T.resolve? name = some (i.castLE f.down.length_le) := by
  unfold Signature.resolve? at h ⊢
  apply Option.map_injective Fin.val_injective
  rw [← List.findIdx?_eq_map_findFinIdx?_val]
  apply f.down.findIdx?_eq_some
  rw [List.findIdx?_eq_map_findFinIdx?_val, h]
  rfl

end Silmaril.Proofs.ProofFormats.LeanNDJSON.MLTT
