module

public import Silmaril.Logic.Matching.GeneralFixedPoint.SortNaturality.Defs

set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace Silmaril.Logic.Matching.GeneralFixedPoint.SortNaturality
open CategoryTheory
open Algebraic.ManySorted (Signature)
open FixedPoint (Ren)
open FixedPoint.SortNaturality (mapRen mapRen_shift mapRen_lift mapRen_liftHead pattern_renameFirstOrder)

private theorem renameSets_heq {S : Type} {A : Signature S}
    {r l k : Nat} {P : Fin r → S} {Q R : Fin l → S} {Γ : Fin k → S} {s : S}
    (h : Q = R) (p : Pattern A P Γ s) (ρ : Ren P Q) (τ : Ren P R)
    (hρ : HEq ρ τ) : HEq (p.renameSets ρ) (p.renameSets τ) := by
  cases h
  cases hρ
  rfl

private theorem mu_heq {S : Type} {A : Signature S} {r k : Nat}
    {P Q : Fin (r+1) → S} {Γ : Fin k → S} (h : P = Q)
    (p : Pattern A P Γ (P 0)) (q : Pattern A Q Γ (Q 0)) (hp : HEq p q) :
    HEq (Pattern.mu p) (Pattern.mu q) := by
  cases h
  cases hp
  rfl

private theorem nu_heq {S : Type} {A : Signature S} {r k : Nat}
    {P Q : Fin (r+1) → S} {Γ : Fin k → S} (h : P = Q)
    (p : Pattern A P Γ (P 0)) (q : Pattern A Q Γ (Q 0)) (hp : HEq p q) :
    HEq (Pattern.nu p) (Pattern.nu q) := by
  cases h
  cases hp
  rfl

/-- Exact syntax equality, including both object binders and native μ/ν.
Only the sort witnesses change; the original variable coordinates are retained. -/
theorem generalPattern_renameSets {B C : SortMaps.Signature} (f : B ⟶ C)
    {r k : Nat} {P : Fin r → B.sorts} {Γ : Fin k → B.sorts} {s : B.sorts}
    (p : Pattern B.symbols P Γ s) :
    ∀ {l : Nat} {Q : Fin l → B.sorts} (ρ : Ren P Q),
      SortMaps.Hom.generalPattern f (p.renameSets ρ) =
        (SortMaps.Hom.generalPattern f p).renameSets (mapRen f ρ) := by
  induction p with
  | base p => intro l Q ρ; rfl
  | @setvar r k P Γ i =>
      intro l Q ρ
      simpa only [Pattern.renameSets, SortMaps.Hom.generalPattern, mapRen] using
        (generalPattern_sort_cast f (ρ i).property
          (.setvar (ρ i).val : Pattern B.symbols Q Γ (Q (ρ i).val)))
  | app op args ih =>
      intro l Q ρ
      exact congrArg (Pattern.app (f.operations op)) (funext (fun i => ih i ρ))
  | neg p hp =>
      intro l Q ρ
      exact congrArg Pattern.neg (hp ρ)
  | conj p q hp hq =>
      intro l Q ρ
      exact congrArg₂ Pattern.conj (hp ρ) (hq ρ)
  | @ex r k P Γ s bound p hp =>
      intro l Q ρ
      change Pattern.ex (f.sorts bound)
        ((SortMaps.Hom.map_cons f bound Γ) ▸
          SortMaps.Hom.generalPattern f (p.renameSets ρ)) =
        Pattern.ex (f.sorts bound)
          (((SortMaps.Hom.map_cons f bound Γ) ▸
            SortMaps.Hom.generalPattern f p).renameSets (mapRen f ρ))
      rw [renameSets_objects_cast, hp ρ]
  | @mu r k P' Γ p hp =>
      intro l Q ρ
      apply eq_of_heq
      apply mu_heq (SortMaps.Hom.map_cons f (P' 0) Q)
      exact (heq_of_eq (hp (Ren.liftHead ρ))).trans
        (renameSets_heq (SortMaps.Hom.map_cons f (P' 0) Q)
          (SortMaps.Hom.generalPattern f p) _ _ (mapRen_liftHead f ρ))
  | @nu r k P' Γ p hp =>
      intro l Q ρ
      apply eq_of_heq
      apply nu_heq (SortMaps.Hom.map_cons f (P' 0) Q)
      exact (heq_of_eq (hp (Ren.liftHead ρ))).trans
        (renameSets_heq (SortMaps.Hom.map_cons f (P' 0) Q)
          (SortMaps.Hom.generalPattern f p) _ _ (mapRen_liftHead f ρ))

end Silmaril.Logic.Matching.GeneralFixedPoint.SortNaturality
