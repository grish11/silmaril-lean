module

public import Silmaril.Logic.Matching.FixedPoint.Variables.Thms
public import Silmaril.Logic.Matching.SortMaps.Thms

/-! Exact sorted-renaming and transport bridges for future syntactic compiler
naturality. No injectivity of the signature sort map is required. -/
@[expose] public section
namespace Silmaril.Logic.Matching.FixedPoint.SortNaturality
open CategoryTheory
open Algebraic.ManySorted (Signature)

/-- Change the sort witnesses while retaining every original variable index. -/
def mapRen {B C : SortMaps.Signature} (f : B ⟶ C)
    {r l : Nat} {P : Fin r → B.sorts} {Q : Fin l → B.sorts} (ρ : Ren P Q) :
    Ren (f.sorts ∘ P) (f.sorts ∘ Q) :=
  fun i => ⟨(ρ i).val, congrArg f.sorts (ρ i).property⟩

theorem mapRen_val {B C : SortMaps.Signature} (f : B ⟶ C)
    {r l : Nat} {P : Fin r → B.sorts} {Q : Fin l → B.sorts} (ρ : Ren P Q) (i : Fin r) :
    (mapRen f ρ i).val = (ρ i).val := rfl

private theorem transport_comp {S T : Type} (f : S → T) (D : T → Type)
    {s t : S} (h : s = t) (x : D (f s)) :
    (congrArg f h ▸ x : D (f t)) = (h ▸ x : D (f t)) := by
  cases h
  rfl

/-- Actual dependent environment pullback is unchanged by reindexing its sort witnesses. -/
theorem pull_mapRen {B C : SortMaps.Signature} (f : B ⟶ C) (D : C.sorts → Type)
    {r l : Nat} {P : Fin r → B.sorts} {Q : Fin l → B.sorts}
    (ρ : Ren P Q) (η : ∀ j, D (f.sorts (Q j))) :
    Ren.pull D η (mapRen f ρ) = Ren.pull (D ∘ f.sorts) η ρ := by
  funext i
  exact transport_comp f.sorts D (ρ i).property (η (ρ i).val)

private theorem ren_heq {S : Type} {r l : Nat}
    {P P' : Fin r → S} {Q Q' : Fin l → S}
    (hP : P = P') (hQ : Q = Q') (ρ : Ren P Q) (τ : Ren P' Q')
    (h : ∀ i, (ρ i).val = (τ i).val) : HEq ρ τ := by
  cases hP
  cases hQ
  apply heq_of_eq
  funext i
  exact Subtype.ext (h i)

/-- The heterogeneous form records the real mapped binder-context transport. -/
theorem mapRen_shift {B C : SortMaps.Signature} (f : B ⟶ C)
    {r : Nat} (P : Fin r → B.sorts) (s : B.sorts) :
    HEq (mapRen f (Ren.shift P s)) (Ren.shift (f.sorts ∘ P) (f.sorts s)) := by
  apply ren_heq rfl (SortMaps.Hom.map_cons f s P)
  intro i
  rfl

theorem mapRen_lift {B C : SortMaps.Signature} (f : B ⟶ C)
    {r l : Nat} {P : Fin r → B.sorts} {Q : Fin l → B.sorts}
    (ρ : Ren P Q) (s : B.sorts) :
    HEq (mapRen f (ρ.lift s)) ((mapRen f ρ).lift (f.sorts s)) := by
  apply ren_heq (SortMaps.Hom.map_cons f s P) (SortMaps.Hom.map_cons f s Q)
  intro i
  exact Fin.cases rfl (fun _ => rfl) i

theorem mapRen_liftHead {B C : SortMaps.Signature} (f : B ⟶ C)
    {r l : Nat} {P' : Fin (r+1) → B.sorts} {Q : Fin l → B.sorts}
    (ρ : Ren (P' ∘ Fin.succ) Q) :
    HEq (mapRen f (Ren.liftHead ρ))
      (Ren.liftHead (P' := f.sorts ∘ P') (Q := f.sorts ∘ Q) (mapRen f ρ)) := by
  apply ren_heq rfl (SortMaps.Hom.map_cons f (P' 0) Q)
  intro i
  exact Fin.cases rfl (fun _ => rfl) i

theorem fixedPattern_sort_cast {B C : SortMaps.Signature} (f : B ⟶ C)
    {r k : Nat} {P : Fin r → B.sorts} {Γ : Fin k → B.sorts} {s t : B.sorts}
    (h : s = t) (p : Pattern B.symbols P Γ s) :
    SortMaps.Hom.fixedPattern f (h ▸ p : Pattern B.symbols P Γ t) =
      (congrArg f.sorts h ▸ SortMaps.Hom.fixedPattern f p :
        Pattern C.symbols (f.sorts ∘ P) (f.sorts ∘ Γ) (f.sorts t)) := by
  cases h
  rfl

theorem fixedPattern_objects_cast {B C : SortMaps.Signature} (f : B ⟶ C)
    {r k : Nat} {P : Fin r → B.sorts} {Γ Δ : Fin k → B.sorts} {s : B.sorts}
    (h : Γ = Δ) (p : Pattern B.symbols P Γ s) :
    SortMaps.Hom.fixedPattern f (h ▸ p : Pattern B.symbols P Δ s) =
      (congrArg (fun ctx => f.sorts ∘ ctx) h ▸ SortMaps.Hom.fixedPattern f p :
        Pattern C.symbols (f.sorts ∘ P) (f.sorts ∘ Δ) (f.sorts s)) := by
  cases h
  rfl

theorem fixedPattern_sets_cast {B C : SortMaps.Signature} (f : B ⟶ C)
    {r k : Nat} {P Q : Fin r → B.sorts} {Γ : Fin k → B.sorts} {s : B.sorts}
    (h : P = Q) (p : Pattern B.symbols P Γ s) :
    SortMaps.Hom.fixedPattern f (h ▸ p : Pattern B.symbols Q Γ s) =
      (congrArg (fun ctx => f.sorts ∘ ctx) h ▸ SortMaps.Hom.fixedPattern f p :
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

end Silmaril.Logic.Matching.FixedPoint.SortNaturality
