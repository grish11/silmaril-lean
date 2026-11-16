module

public import Silmaril.Logic.CommonLogic.Source.Thms

@[expose] public section
namespace Silmaril.Logic.CommonLogic.Source
open CategoryTheory

/-- Preserve successful class-sensitive lookups. Fresh target declarations are
allowed, as are semantic symbol identifications. The reference clause prevents
a new discourse spelling from shadowing an old nondiscourse declaration. -/
structure Names.Supports {S T : Core.Signature} (a : Names S) (b : Names T) (f : S ⟶ T) : Prop where
  discourse : ∀ x d, find? x a.discourse = some d → find? x b.discourse = some (f.discourse d)
  nondiscourse : ∀ x d, find? x a.discourse = none → find? x a.nondiscourse = some d →
    find? x b.discourse = none ∧ find? x b.nondiscourse = some (f.nondiscourse d)
  marker : ∀ x d, find? x a.marker = some d → find? x b.marker = some (f.marker d)

 theorem Names.Supports.refl {S : Core.Signature} (a : Names S) : a.Supports a (𝟙 S) :=
  ⟨fun _ _ h => h, fun _ _ hn h => ⟨hn, h⟩, fun _ _ h => h⟩

theorem Names.Supports.trans {S T U : Core.Signature} {a : Names S} {b : Names T} {c : Names U}
    {f : S ⟶ T} {g : T ⟶ U} (h : a.Supports b f) (k : b.Supports c g) :
    a.Supports c (f ≫ g) where
  discourse x d hd := k.discourse x _ (h.discourse x d hd)
  nondiscourse x d hn hd := by
    obtain ⟨hn', hd'⟩ := h.nondiscourse x d hn hd
    exact k.nondiscourse x _ hn' hd'
  marker x d hd := k.marker x _ (h.marker x d hd)

theorem Names.supports_map {S T : Core.Signature} (a : Names S) (f : S ⟶ T) :
    a.Supports (a.map f) f where
  discourse x d h := by simp only [Names.map, find?_map, h, Option.map_some]
  nondiscourse x d hn h := by simp [Names.map, find?_map, hn, h]
  marker x d h := by simp only [Names.map, find?_map, h, Option.map_some]

end Silmaril.Logic.CommonLogic.Source
