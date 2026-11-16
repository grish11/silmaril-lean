module

public import Silmaril.Logic.Matching.GeneralFixedPoint.SortNaturality.Defs

set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace Silmaril.Logic.Matching.GeneralFixedPoint.SortNaturality
open CategoryTheory
open Algebraic.ManySorted (Signature)
open FixedPoint (Ren)
open FixedPoint.SortNaturality (mapRen mapRen_shift mapRen_lift mapRen_liftHead pattern_renameFirstOrder)

private theorem renameObjects_contexts {S : Type} {A : Signature S}
    {r k l : Nat} {P : Fin r → S} {Γ Γ' : Fin k → S}
    {Δ Δ' : Fin l → S} {s : S}
    (hΓ : Γ = Γ') (hΔ : Δ = Δ') (p : Pattern A P Γ s)
    (ρ : Ren Γ Δ) (τ : Ren Γ' Δ') (hρ : HEq ρ τ) :
    (hΔ ▸ p.renameObjects ρ : Pattern A P Δ' s) =
      (hΓ ▸ p : Pattern A P Γ' s).renameObjects τ := by
  cases hΓ
  cases hΔ
  cases hρ
  rfl

/-- Literal fixed-point syntax, retaining every object-variable coordinate. -/
theorem generalPattern_renameObjects {B C : SortMaps.Signature} (f : B ⟶ C)
    {r k : Nat} {P : Fin r → B.sorts} {Γ : Fin k → B.sorts} {s : B.sorts}
    (p : Pattern B.symbols P Γ s) :
    ∀ {l : Nat} {Δ : Fin l → B.sorts} (ρ : Ren Γ Δ),
      SortMaps.Hom.generalPattern f (p.renameObjects ρ) =
        (SortMaps.Hom.generalPattern f p).renameObjects (mapRen f ρ) := by
  induction p with
  | base p =>
      intro l Δ ρ
      exact congrArg Pattern.base (pattern_renameFirstOrder f p ρ)
  | setvar i => intro l Δ ρ; rfl
  | app op args ih =>
      intro l Δ ρ
      exact congrArg (Pattern.app (f.operations op)) (funext (fun i => ih i ρ))
  | neg p hp =>
      intro l Δ ρ
      exact congrArg Pattern.neg (hp ρ)
  | conj p q hp hq =>
      intro l Δ ρ
      exact congrArg₂ Pattern.conj (hp ρ) (hq ρ)
  | @ex r k P Γ s bound p hp =>
      intro l Δ ρ
      change Pattern.ex (f.sorts bound)
        ((SortMaps.Hom.map_cons f bound Δ) ▸
          SortMaps.Hom.generalPattern f (p.renameObjects (ρ.lift bound))) =
        Pattern.ex (f.sorts bound)
          (((SortMaps.Hom.map_cons f bound Γ) ▸
            SortMaps.Hom.generalPattern f p).renameObjects ((mapRen f ρ).lift (f.sorts bound)))
      rw [hp]
      exact congrArg (Pattern.ex (f.sorts bound))
        (renameObjects_contexts (SortMaps.Hom.map_cons f bound Γ)
          (SortMaps.Hom.map_cons f bound Δ) (SortMaps.Hom.generalPattern f p)
          _ _ (mapRen_lift f ρ bound))
  | mu p hp =>
      intro l Δ ρ
      exact congrArg Pattern.mu (hp ρ)
  | nu p hp =>
      intro l Δ ρ
      exact congrArg Pattern.nu (hp ρ)

end Silmaril.Logic.Matching.GeneralFixedPoint.SortNaturality
