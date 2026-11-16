module

public import Silmaril.Logic.Matching.GuardedLFP.Structure

@[expose] public section
namespace Silmaril.Logic.Matching.GuardedLFP
open CategoryTheory
variable {A B : SortMaps.Signature}

def transportRen {S : Type} {k l : Nat} {Γ Γ' : Fin k → S} {Δ Δ' : Fin l → S}
    (hΓ : Γ = Γ') (hΔ : Δ = Δ') (ρ : FixedPoint.Ren Γ Δ) : FixedPoint.Ren Γ' Δ' := hΓ ▸ hΔ ▸ ρ

theorem transportRen_val {S : Type} {k l : Nat} {Γ Γ' : Fin k → S} {Δ Δ' : Fin l → S}
    (hΓ : Γ = Γ') (hΔ : Δ = Δ') (ρ : FixedPoint.Ren Γ Δ) (i : Fin k) :
    (transportRen hΓ hΔ ρ i).val = (ρ i).val := by cases hΓ; cases hΔ; rfl

def mapRen (f : A ⟶ B) {k l : Nat} {Γ : Fin k → A.sorts} {Δ : Fin l → A.sorts}
    (ρ : FixedPoint.Ren Γ Δ) : FixedPoint.Ren (f.sorts ∘ Γ) (f.sorts ∘ Δ) :=
  fun i => ⟨(ρ i).val, congrArg f.sorts (ρ i).property⟩

theorem mapRen_lift (f : A ⟶ B) {k l : Nat} {Γ : Fin k → A.sorts} {Δ : Fin l → A.sorts}
    (ρ : FixedPoint.Ren Γ Δ) (s : A.sorts) :
    transportRen (SortMaps.Hom.map_cons f s Γ) (SortMaps.Hom.map_cons f s Δ) (mapRen f (ρ.lift s)) =
      (mapRen f ρ).lift (f.sorts s) := by
  funext i
  apply Subtype.ext
  rw [transportRen_val]
  exact Fin.cases rfl (fun _ => rfl) i

theorem renameFO_context {S : Type} {A : Algebraic.ManySorted.Signature S}
    {k l : Nat} {Γ Γ' : Fin k → S} {Δ Δ' : Fin l → S} {s : S}
    (hΓ : Γ = Γ') (hΔ : Δ = Δ') (p : FirstOrder.Pattern A Γ s) (ρ : FixedPoint.Ren Γ Δ) :
    FixedPoint.renameFirstOrder (hΓ ▸ p) (transportRen hΓ hΔ ρ) =
      hΔ ▸ FixedPoint.renameFirstOrder p ρ := by cases hΓ; cases hΔ; rfl

theorem rename_context {S : Type} {A : Algebraic.ManySorted.Signature S}
    {r k l : Nat} {P : Fin r → S} {Γ Γ' : Fin k → S} {Δ Δ' : Fin l → S} {s : S}
    (hΓ : Γ = Γ') (hΔ : Δ = Δ') (p : FixedPoint.Pattern A P Γ s) (ρ : FixedPoint.Ren Γ Δ) :
    (hΓ ▸ p).renameObjects (transportRen hΓ hΔ ρ) = hΔ ▸ p.renameObjects ρ := by
  cases hΓ; cases hΔ; rfl

theorem pattern_sort_cast (f : A ⟶ B) {k : Nat} {Γ : Fin k → A.sorts} {s t : A.sorts}
    (h : s = t) (p : FirstOrder.Pattern A.symbols Γ s) :
    f.pattern (h ▸ p) = congrArg f.sorts h ▸ f.pattern p := by cases h; rfl

theorem pattern_rename (f : A ⟶ B) {k : Nat} {Γ : Fin k → A.sorts} {s : A.sorts}
    (p : FirstOrder.Pattern A.symbols Γ s) :
    ∀ {l : Nat} {Δ : Fin l → A.sorts} (ρ : FixedPoint.Ren Γ Δ),
      f.pattern (FixedPoint.renameFirstOrder p ρ) =
        FixedPoint.renameFirstOrder (f.pattern p) (mapRen f ρ) := by
  induction p with
  | var i =>
      intro l Δ ρ
      simp only [FixedPoint.renameFirstOrder, pattern_sort_cast]
      rfl
  | app op args ih =>
      intro l Δ ρ
      exact congrArg (FirstOrder.Pattern.app (f.operations op)) (funext fun i => ih i ρ)
  | neg p ih => intro l Δ ρ; exact congrArg FirstOrder.Pattern.neg (ih ρ)
  | conj p q hp hq => intro l Δ ρ; exact congrArg₂ FirstOrder.Pattern.conj (hp ρ) (hq ρ)
  | @ex k Γ s bound p ih =>
      intro l Δ ρ
      change FirstOrder.Pattern.ex (f.sorts bound)
        ((SortMaps.Hom.map_cons f bound Δ) ▸ f.pattern (FixedPoint.renameFirstOrder p (ρ.lift bound))) =
        FirstOrder.Pattern.ex (f.sorts bound)
          (FixedPoint.renameFirstOrder ((SortMaps.Hom.map_cons f bound Γ) ▸ f.pattern p)
            ((mapRen f ρ).lift (f.sorts bound)))
      rw [← mapRen_lift, renameFO_context, ih]

/-- Sort-changing native syntax maps commute exactly with sorted object renaming. -/
theorem fixedPattern_rename (f : A ⟶ B) {r k : Nat} {P : Fin r → A.sorts}
    {Γ : Fin k → A.sorts} {s : A.sorts} (p : FixedPoint.Pattern A.symbols P Γ s) :
    ∀ {l : Nat} {Δ : Fin l → A.sorts} (ρ : FixedPoint.Ren Γ Δ),
      f.fixedPattern (p.renameObjects ρ) = (f.fixedPattern p).renameObjects (mapRen f ρ) := by
  induction p with
  | base p => intro l Δ ρ; exact congrArg FixedPoint.Pattern.base (pattern_rename f p ρ)
  | setvar i => intro l Δ ρ; rfl
  | app op args ih => intro l Δ ρ; exact congrArg (FixedPoint.Pattern.app (f.operations op)) (funext fun i => ih i ρ)
  | dualApp op args ih => intro l Δ ρ; exact congrArg (FixedPoint.Pattern.dualApp (f.operations op)) (funext fun i => ih i ρ)
  | conj p q hp hq => intro l Δ ρ; exact congrArg₂ FixedPoint.Pattern.conj (hp ρ) (hq ρ)
  | disj p q hp hq => intro l Δ ρ; exact congrArg₂ FixedPoint.Pattern.disj (hp ρ) (hq ρ)
  | @ex r k P Γ s bound p ih =>
      intro l Δ ρ
      change FixedPoint.Pattern.ex (f.sorts bound)
        ((SortMaps.Hom.map_cons f bound Δ) ▸ f.fixedPattern (p.renameObjects (ρ.lift bound))) =
        FixedPoint.Pattern.ex (f.sorts bound)
          (((SortMaps.Hom.map_cons f bound Γ) ▸ f.fixedPattern p).renameObjects
            ((mapRen f ρ).lift (f.sorts bound)))
      rw [← mapRen_lift, rename_context, ih]
  | @all r k P Γ s bound p ih =>
      intro l Δ ρ
      change FixedPoint.Pattern.all (f.sorts bound)
        ((SortMaps.Hom.map_cons f bound Δ) ▸ f.fixedPattern (p.renameObjects (ρ.lift bound))) =
        FixedPoint.Pattern.all (f.sorts bound)
          (((SortMaps.Hom.map_cons f bound Γ) ▸ f.fixedPattern p).renameObjects
            ((mapRen f ρ).lift (f.sorts bound)))
      rw [← mapRen_lift, rename_context, ih]
  | mu p ih => intro l Δ ρ; exact congrArg FixedPoint.Pattern.mu (ih ρ)
  | nu p ih => intro l Δ ρ; exact congrArg FixedPoint.Pattern.nu (ih ρ)
end Silmaril.Logic.Matching.GuardedLFP
