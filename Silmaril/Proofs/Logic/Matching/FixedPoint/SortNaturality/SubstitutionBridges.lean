module

public import Silmaril.Proofs.Logic.Matching.FixedPoint.SortNaturality.SetRenaming
public import Silmaril.Proofs.Logic.Matching.FixedPoint.SortNaturality.ObjectRenaming

set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace Silmaril.Logic.Matching.FixedPoint.SortNaturality
open CategoryTheory
open Algebraic.ManySorted (Signature)

private theorem renameObjects_target_cast {S : Type} {A : Signature S}
    {r k l : Nat} {P : Fin r → S} {Γ : Fin k → S}
    {Δ Δ' : Fin l → S} {s : S}
    (h : Δ = Δ') (p : Pattern A P Γ s)
    (ρ : Ren Γ Δ) (τ : Ren Γ Δ') (hρ : HEq ρ τ) :
    (h ▸ p.renameObjects ρ : Pattern A P Δ' s) = p.renameObjects τ := by
  cases h
  cases hρ
  rfl

private theorem renameSets_target_cast {S : Type} {A : Signature S}
    {r k l : Nat} {P : Fin r → S} {Γ : Fin k → S}
    {Q Q' : Fin l → S} {s : S}
    (h : Q = Q') (p : Pattern A P Γ s)
    (ρ : Ren P Q) (τ : Ren P Q') (hρ : HEq ρ τ) :
    (h ▸ p.renameSets ρ : Pattern A Q' Γ s) = p.renameSets τ := by
  cases h
  cases hρ
  rfl

/-- Literal replacement coherence under an object binder, including the
actual transport between the mapped and extended target contexts. -/
theorem fixedPattern_objectShift {B C : SortMaps.Signature} (f : B ⟶ C)
    {r k : Nat} {P : Fin r → B.sorts} {Γ : Fin k → B.sorts}
    {s : B.sorts} (bound : B.sorts) (p : Pattern B.symbols P Γ s) :
    ((SortMaps.Hom.map_cons f bound Γ) ▸
      SortMaps.Hom.fixedPattern f (p.renameObjects (Ren.shift Γ bound)) :
        Pattern C.symbols (f.sorts ∘ P)
          (Fin.cases (f.sorts bound) (f.sorts ∘ Γ)) (f.sorts s)) =
      (SortMaps.Hom.fixedPattern f p).renameObjects
        (Ren.shift (f.sorts ∘ Γ) (f.sorts bound)) := by
  rw [fixedPattern_renameObjects]
  exact renameObjects_target_cast (SortMaps.Hom.map_cons f bound Γ)
    (SortMaps.Hom.fixedPattern f p) _ _ (mapRen_shift f Γ bound)

/-- Literal replacement coherence under a native set binder. Source
coordinates are shifted rather than identified, including under sort collapse. -/
theorem fixedPattern_setShift {B C : SortMaps.Signature} (f : B ⟶ C)
    {r k : Nat} {P : Fin r → B.sorts} {Γ : Fin k → B.sorts}
    {s : B.sorts} (bound : B.sorts) (p : Pattern B.symbols P Γ s) :
    ((SortMaps.Hom.map_cons f bound P) ▸
      SortMaps.Hom.fixedPattern f (p.renameSets (Ren.shift P bound)) :
        Pattern C.symbols (Fin.cases (f.sorts bound) (f.sorts ∘ P))
          (f.sorts ∘ Γ) (f.sorts s)) =
      (SortMaps.Hom.fixedPattern f p).renameSets
        (Ren.shift (f.sorts ∘ P) (f.sorts bound)) := by
  rw [fixedPattern_renameSets]
  exact renameSets_target_cast (SortMaps.Hom.map_cons f bound P)
    (SortMaps.Hom.fixedPattern f p) _ _ (mapRen_shift f P bound)

end Silmaril.Logic.Matching.FixedPoint.SortNaturality
