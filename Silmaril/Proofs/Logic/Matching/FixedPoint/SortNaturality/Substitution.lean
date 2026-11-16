module

public import Silmaril.Proofs.Logic.Matching.FixedPoint.SortNaturality.SubstitutionBridges

set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace Silmaril.Logic.Matching.FixedPoint.SortNaturality
open CategoryTheory
open Algebraic.ManySorted (Signature)

private theorem substituteSets_objects_context {S : Type} {A : Signature S}
    {r l k : Nat} {P : Fin r → S} {Q : Fin l → S}
    {Γ Δ : Fin k → S} {s : S} (h : Γ = Δ) (p : Pattern A P Γ s)
    (σ : ∀ i, Pattern A Q Γ (P i)) (τ : ∀ i, Pattern A Q Δ (P i))
    (hσ : ∀ i, (h ▸ σ i : Pattern A Q Δ (P i)) = τ i) :
    (h ▸ p.substituteSets σ : Pattern A Q Δ s) =
      (h ▸ p : Pattern A P Δ s).substituteSets τ := by
  cases h
  have he : σ = τ := funext hσ
  cases he
  rfl

private theorem replacements_heq {S : Type} {A : Signature S}
    {r l k : Nat} {P : Fin r → S} {Q R : Fin l → S}
    {Γ : Fin k → S} (h : Q = R)
    (σ : ∀ i, Pattern A Q Γ (P i)) (τ : ∀ i, Pattern A R Γ (P i))
    (hσ : ∀ i, HEq (σ i) (τ i)) : HEq σ τ := by
  cases h
  apply heq_of_eq
  funext i
  exact eq_of_heq (hσ i)

private theorem substituteSets_target_heq {S : Type} {A : Signature S}
    {r l k : Nat} {P : Fin r → S} {Q R : Fin l → S}
    {Γ : Fin k → S} {s : S} (h : Q = R) (p : Pattern A P Γ s)
    (σ : ∀ i, Pattern A Q Γ (P i)) (τ : ∀ i, Pattern A R Γ (P i))
    (hσ : HEq σ τ) : HEq (p.substituteSets σ) (p.substituteSets τ) := by
  cases h
  cases hσ
  rfl

private theorem sets_cast_heq {S : Type} {A : Signature S}
    {r k : Nat} {P Q : Fin r → S} {Γ : Fin k → S} {s : S}
    (h : P = Q) (p : Pattern A P Γ s) :
    HEq p (h ▸ p : Pattern A Q Γ s) := by
  cases h
  rfl

private theorem setvar_heq {S : Type} {A : Signature S}
    {r k : Nat} {P Q : Fin r → S} {Γ : Fin k → S}
    (h : P = Q) (i : Fin r) :
    HEq (.setvar i : Pattern A P Γ (P i)) (.setvar i : Pattern A Q Γ (Q i)) := by
  cases h
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

private theorem lifted_replacements_heq {B C : SortMaps.Signature} (f : B ⟶ C)
    {r l k : Nat} {P' : Fin (r+1) → B.sorts} {Q : Fin l → B.sorts}
    {Γ : Fin k → B.sorts}
    (σ : ∀ i : Fin r, Pattern B.symbols Q Γ (P' i.succ)) :
    HEq
      (fun i => SortMaps.Hom.fixedPattern f
        ((Fin.cases (.setvar 0)
          (fun j => (σ j).renameSets (Ren.shift Q (P' 0))) :
            ∀ i, Pattern B.symbols (Fin.cases (P' 0) Q) Γ (P' i)) i))
      (Fin.cases (.setvar 0)
        (fun j => (SortMaps.Hom.fixedPattern f (σ j)).renameSets
          (Ren.shift (f.sorts ∘ Q) (f.sorts (P' 0)))) :
            ∀ i, Pattern C.symbols (Fin.cases (f.sorts (P' 0)) (f.sorts ∘ Q))
              (f.sorts ∘ Γ) (f.sorts (P' i))) := by
  apply replacements_heq (SortMaps.Hom.map_cons f (P' 0) Q)
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact setvar_heq (SortMaps.Hom.map_cons f (P' 0) Q) 0
  · exact (sets_cast_heq (SortMaps.Hom.map_cons f (P' 0) Q) _).trans
      (heq_of_eq (fixedPattern_setShift f (P' 0) (σ j)))

/-- Exact capture-avoiding substitution naturality for arbitrary sort maps.
Object and set binders retain their actual context transports, and all source
replacement coordinates remain indexed by the original finite family. -/
theorem fixedPattern_substituteSets {B C : SortMaps.Signature} (f : B ⟶ C)
    {r k : Nat} {P : Fin r → B.sorts} {Γ : Fin k → B.sorts} {s : B.sorts}
    (p : Pattern B.symbols P Γ s) :
    ∀ {l : Nat} {Q : Fin l → B.sorts} (σ : ∀ i, Pattern B.symbols Q Γ (P i)),
      SortMaps.Hom.fixedPattern f (p.substituteSets σ) =
        (SortMaps.Hom.fixedPattern f p).substituteSets
          (fun i => SortMaps.Hom.fixedPattern f (σ i)) := by
  induction p with
  | base p => intro l Q σ; rfl
  | setvar i => intro l Q σ; rfl
  | app op args ih =>
      intro l Q σ
      exact congrArg (Pattern.app (f.operations op)) (funext (fun i => ih i σ))
  | dualApp op args ih =>
      intro l Q σ
      exact congrArg (Pattern.dualApp (f.operations op)) (funext (fun i => ih i σ))
  | conj p q hp hq =>
      intro l Q σ
      exact congrArg₂ Pattern.conj (hp σ) (hq σ)
  | disj p q hp hq =>
      intro l Q σ
      exact congrArg₂ Pattern.disj (hp σ) (hq σ)
  | @ex r k P Γ s bound p hp =>
      intro l Q σ
      change Pattern.ex (f.sorts bound)
        ((SortMaps.Hom.map_cons f bound Γ) ▸
          SortMaps.Hom.fixedPattern f
            (p.substituteSets (fun i => (σ i).renameObjects (Ren.shift Γ bound)))) =
        Pattern.ex (f.sorts bound)
          (((SortMaps.Hom.map_cons f bound Γ) ▸
            SortMaps.Hom.fixedPattern f p).substituteSets
              (fun i => (SortMaps.Hom.fixedPattern f (σ i)).renameObjects
                (Ren.shift (f.sorts ∘ Γ) (f.sorts bound))))
      rw [hp]
      exact congrArg (Pattern.ex (f.sorts bound))
        (substituteSets_objects_context (SortMaps.Hom.map_cons f bound Γ)
          (SortMaps.Hom.fixedPattern f p) _ _
          (fun i => fixedPattern_objectShift f bound (σ i)))
  | @all r k P Γ s bound p hp =>
      intro l Q σ
      change Pattern.all (f.sorts bound)
        ((SortMaps.Hom.map_cons f bound Γ) ▸
          SortMaps.Hom.fixedPattern f
            (p.substituteSets (fun i => (σ i).renameObjects (Ren.shift Γ bound)))) =
        Pattern.all (f.sorts bound)
          (((SortMaps.Hom.map_cons f bound Γ) ▸
            SortMaps.Hom.fixedPattern f p).substituteSets
              (fun i => (SortMaps.Hom.fixedPattern f (σ i)).renameObjects
                (Ren.shift (f.sorts ∘ Γ) (f.sorts bound))))
      rw [hp]
      exact congrArg (Pattern.all (f.sorts bound))
        (substituteSets_objects_context (SortMaps.Hom.map_cons f bound Γ)
          (SortMaps.Hom.fixedPattern f p) _ _
          (fun i => fixedPattern_objectShift f bound (σ i)))
  | @mu r k P' Γ p hp =>
      intro l Q σ
      let lifted : ∀ i, Pattern B.symbols (Fin.cases (P' 0) Q) Γ (P' i) :=
        Fin.cases (.setvar 0) (fun i => (σ i).renameSets (Ren.shift Q (P' 0)))
      apply eq_of_heq
      apply mu_heq (SortMaps.Hom.map_cons f (P' 0) Q)
      exact (heq_of_eq (hp lifted)).trans
        (substituteSets_target_heq (SortMaps.Hom.map_cons f (P' 0) Q)
          (SortMaps.Hom.fixedPattern f p) _ _ (lifted_replacements_heq f σ))
  | @nu r k P' Γ p hp =>
      intro l Q σ
      let lifted : ∀ i, Pattern B.symbols (Fin.cases (P' 0) Q) Γ (P' i) :=
        Fin.cases (.setvar 0) (fun i => (σ i).renameSets (Ren.shift Q (P' 0)))
      apply eq_of_heq
      apply nu_heq (SortMaps.Hom.map_cons f (P' 0) Q)
      exact (heq_of_eq (hp lifted)).trans
        (substituteSets_target_heq (SortMaps.Hom.map_cons f (P' 0) Q)
          (SortMaps.Hom.fixedPattern f p) _ _ (lifted_replacements_heq f σ))

end Silmaril.Logic.Matching.FixedPoint.SortNaturality
