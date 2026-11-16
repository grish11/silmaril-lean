module

public import Silmaril.Logic.Matching.GeneralFixedPoint.Variables.Thms
public import Silmaril.Logic.Matching.SortMaps.GeneralFixedPoint.Thms
public import Silmaril.Logic.Matching.FixedPoint.SortNaturality.Thms

@[expose] public section
namespace Silmaril.Logic.Matching.GeneralFixedPoint.SortNaturality
open CategoryTheory
open Algebraic.ManySorted (Signature)
open FixedPoint (Ren)
open FixedPoint.SortNaturality (mapRen mapRen_shift mapRen_lift mapRen_liftHead)

theorem generalPattern_sort_cast {B C : SortMaps.Signature} (f : B ⟶ C)
    {r k : Nat} {P : Fin r → B.sorts} {Γ : Fin k → B.sorts} {s t : B.sorts}
    (h : s = t) (p : Pattern B.symbols P Γ s) :
    SortMaps.Hom.generalPattern f (h ▸ p : Pattern B.symbols P Γ t) =
      (congrArg f.sorts h ▸ SortMaps.Hom.generalPattern f p :
        Pattern C.symbols (f.sorts ∘ P) (f.sorts ∘ Γ) (f.sorts t)) := by
  cases h
  rfl

theorem generalPattern_objects_cast {B C : SortMaps.Signature} (f : B ⟶ C)
    {r k : Nat} {P : Fin r → B.sorts} {Γ Δ : Fin k → B.sorts} {s : B.sorts}
    (h : Γ = Δ) (p : Pattern B.symbols P Γ s) :
    SortMaps.Hom.generalPattern f (h ▸ p : Pattern B.symbols P Δ s) =
      (congrArg (fun ctx => f.sorts ∘ ctx) h ▸ SortMaps.Hom.generalPattern f p :
        Pattern C.symbols (f.sorts ∘ P) (f.sorts ∘ Δ) (f.sorts s)) := by
  cases h
  rfl

theorem generalPattern_sets_cast {B C : SortMaps.Signature} (f : B ⟶ C)
    {r k : Nat} {P Q : Fin r → B.sorts} {Γ : Fin k → B.sorts} {s : B.sorts}
    (h : P = Q) (p : Pattern B.symbols P Γ s) :
    SortMaps.Hom.generalPattern f (h ▸ p : Pattern B.symbols Q Γ s) =
      (congrArg (fun ctx => f.sorts ∘ ctx) h ▸ SortMaps.Hom.generalPattern f p :
        Pattern C.symbols (f.sorts ∘ Q) (f.sorts ∘ Γ) (f.sorts s)) := by
  cases h
  rfl

theorem renameSets_objects_cast {S : Type} {A : Signature S}
    {r l k : Nat} {P : Fin r → S} {Q : Fin l → S} {Γ Δ : Fin k → S} {s : S}
    (h : Γ = Δ) (p : Pattern A P Γ s) (ρ : Ren P Q) :
    (h ▸ p : Pattern A P Δ s).renameSets ρ =
      (h ▸ p.renameSets ρ : Pattern A Q Δ s) := by
  cases h
  rfl

theorem renameObjects_sets_cast {S : Type} {A : Signature S}
    {r k l : Nat} {P Q : Fin r → S} {Γ : Fin k → S} {Δ : Fin l → S} {s : S}
    (h : P = Q) (p : Pattern A P Γ s) (ρ : Ren Γ Δ) :
    (h ▸ p : Pattern A Q Γ s).renameObjects ρ =
      (h ▸ p.renameObjects ρ : Pattern A Q Δ s) := by
  cases h
  rfl

end Silmaril.Logic.Matching.GeneralFixedPoint.SortNaturality
