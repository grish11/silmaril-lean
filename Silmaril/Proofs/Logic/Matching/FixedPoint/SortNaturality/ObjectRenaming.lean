module

public import Silmaril.Logic.Matching.FixedPoint.SortNaturality.Defs

set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace Silmaril.Logic.Matching.FixedPoint.SortNaturality
open CategoryTheory
open Algebraic.ManySorted (Signature)

private theorem firstOrder_sort_cast {B C : SortMaps.Signature} (f : B ⟶ C)
    {k : Nat} {Γ : Fin k → B.sorts} {s t : B.sorts}
    (h : s = t) (p : FirstOrder.Pattern B.symbols Γ s) :
    SortMaps.Hom.pattern f (h ▸ p : FirstOrder.Pattern B.symbols Γ t) =
      (congrArg f.sorts h ▸ SortMaps.Hom.pattern f p :
        FirstOrder.Pattern C.symbols (f.sorts ∘ Γ) (f.sorts t)) := by
  cases h
  rfl

private theorem renameFirstOrder_contexts {S : Type} {A : Signature S}
    {k l : Nat} {Γ Γ' : Fin k → S} {Δ Δ' : Fin l → S} {s : S}
    (hΓ : Γ = Γ') (hΔ : Δ = Δ') (p : FirstOrder.Pattern A Γ s)
    (ρ : Ren Γ Δ) (τ : Ren Γ' Δ') (hρ : HEq ρ τ) :
    (hΔ ▸ renameFirstOrder p ρ : FirstOrder.Pattern A Δ' s) =
      renameFirstOrder (hΓ ▸ p : FirstOrder.Pattern A Γ' s) τ := by
  cases hΓ
  cases hΔ
  cases hρ
  rfl

/-- Literal first-order syntax commutes with every sort map. -/
theorem pattern_renameFirstOrder {B C : SortMaps.Signature} (f : B ⟶ C)
    {k : Nat} {Γ : Fin k → B.sorts} {s : B.sorts}
    (p : FirstOrder.Pattern B.symbols Γ s) :
    ∀ {l : Nat} {Δ : Fin l → B.sorts} (ρ : Ren Γ Δ),
      SortMaps.Hom.pattern f (renameFirstOrder p ρ) =
        renameFirstOrder (SortMaps.Hom.pattern f p) (mapRen f ρ) := by
  induction p with
  | var i =>
      intro l Δ ρ
      exact firstOrder_sort_cast f (ρ i).property
        (.var (ρ i).val : FirstOrder.Pattern B.symbols Δ (Δ (ρ i).val))
  | app op args ih =>
      intro l Δ ρ
      exact congrArg (FirstOrder.Pattern.app (f.operations op)) (funext (fun i => ih i ρ))
  | neg p hp =>
      intro l Δ ρ
      exact congrArg FirstOrder.Pattern.neg (hp ρ)
  | conj p q hp hq =>
      intro l Δ ρ
      exact congrArg₂ FirstOrder.Pattern.conj (hp ρ) (hq ρ)
  | @ex k Γ s bound p hp =>
      intro l Δ ρ
      change FirstOrder.Pattern.ex (f.sorts bound)
        ((SortMaps.Hom.map_cons f bound Δ) ▸
          SortMaps.Hom.pattern f (renameFirstOrder p (ρ.lift bound))) =
        FirstOrder.Pattern.ex (f.sorts bound)
          (renameFirstOrder ((SortMaps.Hom.map_cons f bound Γ) ▸
            SortMaps.Hom.pattern f p) ((mapRen f ρ).lift (f.sorts bound)))
      rw [hp]
      exact congrArg (FirstOrder.Pattern.ex (f.sorts bound))
        (renameFirstOrder_contexts (SortMaps.Hom.map_cons f bound Γ)
          (SortMaps.Hom.map_cons f bound Δ) (SortMaps.Hom.pattern f p)
          _ _ (mapRen_lift f ρ bound))

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
theorem fixedPattern_renameObjects {B C : SortMaps.Signature} (f : B ⟶ C)
    {r k : Nat} {P : Fin r → B.sorts} {Γ : Fin k → B.sorts} {s : B.sorts}
    (p : Pattern B.symbols P Γ s) :
    ∀ {l : Nat} {Δ : Fin l → B.sorts} (ρ : Ren Γ Δ),
      SortMaps.Hom.fixedPattern f (p.renameObjects ρ) =
        (SortMaps.Hom.fixedPattern f p).renameObjects (mapRen f ρ) := by
  induction p with
  | base p =>
      intro l Δ ρ
      exact congrArg Pattern.base (pattern_renameFirstOrder f p ρ)
  | setvar i => intro l Δ ρ; rfl
  | app op args ih =>
      intro l Δ ρ
      exact congrArg (Pattern.app (f.operations op)) (funext (fun i => ih i ρ))
  | dualApp op args ih =>
      intro l Δ ρ
      exact congrArg (Pattern.dualApp (f.operations op)) (funext (fun i => ih i ρ))
  | conj p q hp hq =>
      intro l Δ ρ
      exact congrArg₂ Pattern.conj (hp ρ) (hq ρ)
  | disj p q hp hq =>
      intro l Δ ρ
      exact congrArg₂ Pattern.disj (hp ρ) (hq ρ)
  | @ex r k P Γ s bound p hp =>
      intro l Δ ρ
      change Pattern.ex (f.sorts bound)
        ((SortMaps.Hom.map_cons f bound Δ) ▸
          SortMaps.Hom.fixedPattern f (p.renameObjects (ρ.lift bound))) =
        Pattern.ex (f.sorts bound)
          (((SortMaps.Hom.map_cons f bound Γ) ▸
            SortMaps.Hom.fixedPattern f p).renameObjects ((mapRen f ρ).lift (f.sorts bound)))
      rw [hp]
      exact congrArg (Pattern.ex (f.sorts bound))
        (renameObjects_contexts (SortMaps.Hom.map_cons f bound Γ)
          (SortMaps.Hom.map_cons f bound Δ) (SortMaps.Hom.fixedPattern f p)
          _ _ (mapRen_lift f ρ bound))
  | @all r k P Γ s bound p hp =>
      intro l Δ ρ
      change Pattern.all (f.sorts bound)
        ((SortMaps.Hom.map_cons f bound Δ) ▸
          SortMaps.Hom.fixedPattern f (p.renameObjects (ρ.lift bound))) =
        Pattern.all (f.sorts bound)
          (((SortMaps.Hom.map_cons f bound Γ) ▸
            SortMaps.Hom.fixedPattern f p).renameObjects ((mapRen f ρ).lift (f.sorts bound)))
      rw [hp]
      exact congrArg (Pattern.all (f.sorts bound))
        (renameObjects_contexts (SortMaps.Hom.map_cons f bound Γ)
          (SortMaps.Hom.map_cons f bound Δ) (SortMaps.Hom.fixedPattern f p)
          _ _ (mapRen_lift f ρ bound))
  | mu p hp =>
      intro l Δ ρ
      exact congrArg Pattern.mu (hp ρ)
  | nu p hp =>
      intro l Δ ρ
      exact congrArg Pattern.nu (hp ρ)

end Silmaril.Logic.Matching.FixedPoint.SortNaturality
