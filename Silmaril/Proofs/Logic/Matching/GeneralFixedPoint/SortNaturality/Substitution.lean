module

public import Silmaril.Proofs.Logic.Matching.GeneralFixedPoint.SortNaturality.SubstitutionBridges

set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace Silmaril.Logic.Matching.GeneralFixedPoint.SortNaturality
open CategoryTheory
open Algebraic.ManySorted (Signature)
open FixedPoint (Ren)

private theorem objects_cast_heq {S : Type} {A : Signature S}
    {r k : Nat} {P : Fin r → S} {Γ Δ : Fin k → S} {s : S}
    (h : Γ = Δ) (p : Pattern A P Γ s) :
    HEq p (h ▸ p : Pattern A P Δ s) := by
  cases h
  rfl

private theorem firstOrder_objects_cast_heq {S : Type} {A : Signature S}
    {k : Nat} {Γ Δ : Fin k → S} {s : S}
    (h : Γ = Δ) (p : FirstOrder.Pattern A Γ s) :
    HEq p (h ▸ p : FirstOrder.Pattern A Δ s) := by
  cases h
  rfl

private theorem sets_cast_heq {S : Type} {A : Signature S}
    {r k : Nat} {P Q : Fin r → S} {Γ : Fin k → S} {s : S}
    (h : P = Q) (p : Pattern A P Γ s) :
    HEq p (h ▸ p : Pattern A Q Γ s) := by
  cases h
  rfl

private theorem families_heq {S : Type} {A : Signature S}
    {r a b : Nat} {R R' : Fin r → S} {Q Q' : Fin a → S} {Δ Δ' : Fin b → S}
    (hR : R = R') (hQ : Q = Q') (hΔ : Δ = Δ')
    (xs : ∀ i, Pattern A Q Δ (R i)) (ys : ∀ i, Pattern A Q' Δ' (R' i))
    (same : ∀ i, HEq (xs i) (ys i)) : HEq xs ys := by
  cases hR
  cases hQ
  cases hΔ
  apply heq_of_eq
  funext i
  exact eq_of_heq (same i)

private theorem substitute_heq {S : Type} {A : Signature S}
    {r k a b : Nat} {P P' : Fin r → S} {Γ Γ' : Fin k → S}
    {Q Q' : Fin a → S} {Δ Δ' : Fin b → S} {s : S}
    (hP : P = P') (hΓ : Γ = Γ') (hQ : Q = Q') (hΔ : Δ = Δ')
    (p : Pattern A P Γ s) (p' : Pattern A P' Γ' s) (hp : HEq p p')
    (σ : ∀ i, Pattern A Q Δ (P i)) (σ' : ∀ i, Pattern A Q' Δ' (P' i))
    (hσ : HEq σ σ')
    (τ : ∀ i, Pattern A Q Δ (Γ i)) (τ' : ∀ i, Pattern A Q' Δ' (Γ' i))
    (hτ : HEq τ τ') : HEq (p.substitute σ τ) (p'.substitute σ' τ') := by
  cases hP
  cases hΓ
  cases hQ
  cases hΔ
  cases hp
  cases hσ
  cases hτ
  rfl

private theorem firstOrder_substitute_heq {S : Type} {A : Signature S}
    {k a b : Nat} {Γ Γ' : Fin k → S}
    {Q Q' : Fin a → S} {Δ Δ' : Fin b → S} {s : S}
    (hΓ : Γ = Γ') (hQ : Q = Q') (hΔ : Δ = Δ')
    (p : FirstOrder.Pattern A Γ s) (p' : FirstOrder.Pattern A Γ' s) (hp : HEq p p')
    (τ : ∀ i, Pattern A Q Δ (Γ i)) (τ' : ∀ i, Pattern A Q' Δ' (Γ' i))
    (hτ : HEq τ τ') : HEq (substituteFirstOrder p τ) (substituteFirstOrder p' τ') := by
  cases hΓ
  cases hQ
  cases hΔ
  cases hp
  cases hτ
  rfl

private theorem basevar_heq {S : Type} {A : Signature S}
    {r k : Nat} {P Q : Fin r → S} {Γ Δ : Fin k → S}
    (hP : P = Q) (hΓ : Γ = Δ) (i : Fin k) :
    HEq (.base (.var i) : Pattern A P Γ (Γ i)) (.base (.var i) : Pattern A Q Δ (Δ i)) := by
  cases hP
  cases hΓ
  rfl

private theorem setvar_heq {S : Type} {A : Signature S}
    {r k : Nat} {P Q : Fin r → S} {Γ : Fin k → S}
    (hP : P = Q) (i : Fin r) :
    HEq (.setvar i : Pattern A P Γ (P i)) (.setvar i : Pattern A Q Γ (Q i)) := by
  cases hP
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

private theorem object_shift_heq {B C : SortMaps.Signature} (f : B ⟶ C)
    {r k : Nat} {P : Fin r → B.sorts} {Γ : Fin k → B.sorts} {s : B.sorts}
    (bound : B.sorts) (p : Pattern B.symbols P Γ s) :
    HEq (SortMaps.Hom.generalPattern f (p.renameObjects (Ren.shift Γ bound)))
      ((SortMaps.Hom.generalPattern f p).renameObjects
        (Ren.shift (f.sorts ∘ Γ) (f.sorts bound))) :=
  (objects_cast_heq (SortMaps.Hom.map_cons f bound Γ) _).trans
    (heq_of_eq (generalPattern_objectShift f bound p))

private theorem set_shift_heq {B C : SortMaps.Signature} (f : B ⟶ C)
    {r k : Nat} {P : Fin r → B.sorts} {Γ : Fin k → B.sorts} {s : B.sorts}
    (bound : B.sorts) (p : Pattern B.symbols P Γ s) :
    HEq (SortMaps.Hom.generalPattern f (p.renameSets (Ren.shift P bound)))
      ((SortMaps.Hom.generalPattern f p).renameSets
        (Ren.shift (f.sorts ∘ P) (f.sorts bound))) :=
  (sets_cast_heq (SortMaps.Hom.map_cons f bound P) _).trans
    (heq_of_eq (generalPattern_setShift f bound p))

private theorem lifted_objects_heq {B C : SortMaps.Signature} (f : B ⟶ C)
    {k a b : Nat} {Γ : Fin k → B.sorts} {Q : Fin a → B.sorts}
    {Δ : Fin b → B.sorts} (bound : B.sorts)
    (τ : ∀ i, Pattern B.symbols Q Δ (Γ i)) :
    HEq
      (fun i => SortMaps.Hom.generalPattern f
        ((Fin.cases (.base (.var 0))
          (fun j => (τ j).renameObjects (Ren.shift Δ bound)) :
            ∀ i, Pattern B.symbols Q (Fin.cases bound Δ) (Fin.cases bound Γ i)) i))
      (Fin.cases (.base (.var 0))
        (fun j => (SortMaps.Hom.generalPattern f (τ j)).renameObjects
          (Ren.shift (f.sorts ∘ Δ) (f.sorts bound))) :
            ∀ i, Pattern C.symbols (f.sorts ∘ Q)
              (Fin.cases (f.sorts bound) (f.sorts ∘ Δ))
              (Fin.cases (f.sorts bound) (f.sorts ∘ Γ) i)) := by
  apply families_heq (SortMaps.Hom.map_cons f bound Γ) rfl (SortMaps.Hom.map_cons f bound Δ)
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact basevar_heq rfl (SortMaps.Hom.map_cons f bound Δ) 0
  · exact object_shift_heq f bound (τ j)

/-- The full first-order leaf substitution commutes with arbitrary sort maps,
including fresh object binders and their capture-avoiding shifts. -/
theorem generalPattern_substituteFirstOrder {B C : SortMaps.Signature} (f : B ⟶ C)
    {k : Nat} {Γ : Fin k → B.sorts} {s : B.sorts}
    (p : FirstOrder.Pattern B.symbols Γ s) :
    ∀ {a b : Nat} {Q : Fin a → B.sorts} {Δ : Fin b → B.sorts}
      (τ : ∀ i, Pattern B.symbols Q Δ (Γ i)),
      SortMaps.Hom.generalPattern f (substituteFirstOrder p τ) =
        substituteFirstOrder (SortMaps.Hom.pattern f p)
          (fun i => SortMaps.Hom.generalPattern f (τ i)) := by
  induction p with
  | var i => intro a b Q Δ τ; rfl
  | app op args ih =>
      intro a b Q Δ τ
      exact congrArg (Pattern.app (f.operations op)) (funext (fun i => ih i τ))
  | neg p hp =>
      intro a b Q Δ τ
      exact congrArg Pattern.neg (hp τ)
  | conj p q hp hq =>
      intro a b Q Δ τ
      exact congrArg₂ Pattern.conj (hp τ) (hq τ)
  | @ex k Γ s bound p hp =>
      intro a b Q Δ τ
      change Pattern.ex (f.sorts bound)
        ((SortMaps.Hom.map_cons f bound Δ) ▸
          SortMaps.Hom.generalPattern f
            (substituteFirstOrder (Γ := Fin.cases bound Γ)
              (Q := Q) (Δ := Fin.cases bound Δ) p
              (Fin.cases (.base (.var 0))
                (fun i => (τ i).renameObjects (Ren.shift Δ bound))))) =
        Pattern.ex (f.sorts bound)
          (substituteFirstOrder (Γ := Fin.cases (f.sorts bound) (f.sorts ∘ Γ))
            (Q := f.sorts ∘ Q)
            (Δ := Fin.cases (f.sorts bound) (f.sorts ∘ Δ))
            ((SortMaps.Hom.map_cons f bound Γ) ▸ SortMaps.Hom.pattern f p)
            (Fin.cases (.base (.var 0))
              (fun i => (SortMaps.Hom.generalPattern f (τ i)).renameObjects
                (Ren.shift (f.sorts ∘ Δ) (f.sorts bound)))))
      apply congrArg (Pattern.ex (f.sorts bound))
      apply eq_of_heq
      exact (objects_cast_heq (SortMaps.Hom.map_cons f bound Δ) _).symm.trans
        ((heq_of_eq (hp _)).trans
          (firstOrder_substitute_heq (SortMaps.Hom.map_cons f bound Γ) rfl
            (SortMaps.Hom.map_cons f bound Δ) _ _
            (firstOrder_objects_cast_heq (SortMaps.Hom.map_cons f bound Γ) _) _ _ (lifted_objects_heq f bound τ)))

private theorem lifted_sets_heq {B C : SortMaps.Signature} (f : B ⟶ C)
    {r a b : Nat} {P' : Fin (r+1) → B.sorts} {Q : Fin a → B.sorts}
    {Δ : Fin b → B.sorts}
    (σ : ∀ i : Fin r, Pattern B.symbols Q Δ (P' i.succ)) :
    HEq
      (fun i => SortMaps.Hom.generalPattern f
        ((Fin.cases (.setvar 0)
          (fun j => (σ j).renameSets (Ren.shift Q (P' 0))) :
            ∀ i, Pattern B.symbols (Fin.cases (P' 0) Q) Δ (P' i)) i))
      (Fin.cases (.setvar 0)
        (fun j => (SortMaps.Hom.generalPattern f (σ j)).renameSets
          (Ren.shift (f.sorts ∘ Q) (f.sorts (P' 0)))) :
            ∀ i, Pattern C.symbols (Fin.cases (f.sorts (P' 0)) (f.sorts ∘ Q))
              (f.sorts ∘ Δ) (f.sorts (P' i))) := by
  apply families_heq rfl (SortMaps.Hom.map_cons f (P' 0) Q) rfl
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact setvar_heq (SortMaps.Hom.map_cons f (P' 0) Q) 0
  · exact set_shift_heq f (P' 0) (σ j)

/-- Exact simultaneous substitution naturality for the full Boolean and μ/ν
syntax. Both namespaces are shifted under their binders; neither sort-map
injectivity nor a condition on free-variable occurrence is needed. -/
theorem generalPattern_substitute {B C : SortMaps.Signature} (f : B ⟶ C)
    {r k : Nat} {P : Fin r → B.sorts} {Γ : Fin k → B.sorts} {s : B.sorts}
    (p : Pattern B.symbols P Γ s) :
    ∀ {a b : Nat} {Q : Fin a → B.sorts} {Δ : Fin b → B.sorts}
      (σ : ∀ i, Pattern B.symbols Q Δ (P i))
      (τ : ∀ i, Pattern B.symbols Q Δ (Γ i)),
      SortMaps.Hom.generalPattern f (p.substitute σ τ) =
        (SortMaps.Hom.generalPattern f p).substitute
          (fun i => SortMaps.Hom.generalPattern f (σ i))
          (fun i => SortMaps.Hom.generalPattern f (τ i)) := by
  induction p with
  | base p => intro a b Q Δ σ τ; exact generalPattern_substituteFirstOrder f p τ
  | setvar i => intro a b Q Δ σ τ; rfl
  | app op args ih =>
      intro a b Q Δ σ τ
      exact congrArg (Pattern.app (f.operations op)) (funext (fun i => ih i σ τ))
  | neg p hp =>
      intro a b Q Δ σ τ
      exact congrArg Pattern.neg (hp σ τ)
  | conj p q hp hq =>
      intro a b Q Δ σ τ
      exact congrArg₂ Pattern.conj (hp σ τ) (hq σ τ)
  | @ex r k P Γ s bound p hp =>
      intro a b Q Δ σ τ
      change Pattern.ex (f.sorts bound)
        ((SortMaps.Hom.map_cons f bound Δ) ▸
          SortMaps.Hom.generalPattern f
            (p.substitute (fun i => (σ i).renameObjects (Ren.shift Δ bound))
              (Fin.cases (.base (.var 0))
                (fun i => (τ i).renameObjects (Ren.shift Δ bound))))) =
        Pattern.ex (f.sorts bound)
          (((SortMaps.Hom.map_cons f bound Γ) ▸ SortMaps.Hom.generalPattern f p).substitute
            (fun i => (SortMaps.Hom.generalPattern f (σ i)).renameObjects
              (Ren.shift (f.sorts ∘ Δ) (f.sorts bound)))
            (Fin.cases (.base (.var 0))
              (fun i => (SortMaps.Hom.generalPattern f (τ i)).renameObjects
                (Ren.shift (f.sorts ∘ Δ) (f.sorts bound)))))
      apply congrArg (Pattern.ex (f.sorts bound))
      apply eq_of_heq
      exact (objects_cast_heq (SortMaps.Hom.map_cons f bound Δ) _).symm.trans
        ((heq_of_eq (hp _ _)).trans
          (substitute_heq rfl (SortMaps.Hom.map_cons f bound Γ) rfl
            (SortMaps.Hom.map_cons f bound Δ) _ _
            (objects_cast_heq (SortMaps.Hom.map_cons f bound Γ) _) _ _
            (families_heq rfl rfl (SortMaps.Hom.map_cons f bound Δ) _ _
              (fun i => object_shift_heq f bound (σ i))) _ _ (lifted_objects_heq f bound τ)))
  | @mu r k P' Γ p hp =>
      intro a b Q Δ σ τ
      let σ' : ∀ i, Pattern B.symbols (Fin.cases (P' 0) Q) Δ (P' i) :=
        Fin.cases (.setvar 0) (fun i => (σ i).renameSets (Ren.shift Q (P' 0)))
      let τ' := fun i => (τ i).renameSets (Ren.shift Q (P' 0))
      apply eq_of_heq
      apply mu_heq (SortMaps.Hom.map_cons f (P' 0) Q)
      exact (heq_of_eq (hp σ' τ')).trans
        (substitute_heq rfl rfl (SortMaps.Hom.map_cons f (P' 0) Q) rfl _ _ HEq.rfl
          _ _ (lifted_sets_heq f σ) _ _
          (families_heq rfl (SortMaps.Hom.map_cons f (P' 0) Q) rfl _ _
            (fun i => set_shift_heq f (P' 0) (τ i))))
  | @nu r k P' Γ p hp =>
      intro a b Q Δ σ τ
      let σ' : ∀ i, Pattern B.symbols (Fin.cases (P' 0) Q) Δ (P' i) :=
        Fin.cases (.setvar 0) (fun i => (σ i).renameSets (Ren.shift Q (P' 0)))
      let τ' := fun i => (τ i).renameSets (Ren.shift Q (P' 0))
      apply eq_of_heq
      apply nu_heq (SortMaps.Hom.map_cons f (P' 0) Q)
      exact (heq_of_eq (hp σ' τ')).trans
        (substitute_heq rfl rfl (SortMaps.Hom.map_cons f (P' 0) Q) rfl _ _ HEq.rfl
          _ _ (lifted_sets_heq f σ) _ _
          (families_heq rfl (SortMaps.Hom.map_cons f (P' 0) Q) rfl _ _
            (fun i => set_shift_heq f (P' 0) (τ i))))

end Silmaril.Logic.Matching.GeneralFixedPoint.SortNaturality
