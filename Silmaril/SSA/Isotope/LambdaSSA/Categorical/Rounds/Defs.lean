module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Defs

/-! # Rounds of a step, and the phase systems that unroll them -/

@[expose] public section

universe v u

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]

/-- `roundsStep h n` runs up to `n + 1` rounds of `h`, stopping at the first return. -/
noncomputable def roundsStep {X Y : C} (h : X ⟶ Y ⨿ X) : Nat → (X ⟶ Y ⨿ X)
  | 0 => h
  | n + 1 => h ≫ coprod.desc coprod.inl (roundsStep h n)

variable (C) in
/-- What the phase-counter argument for unrolling uses.

* An iterator with the fixpoint, naturality and codiagonal laws.
* Objects `obj k` of `k + 1` phases of the state `obj 0`, each presented as
  a sum of the state and the previous object.
* Uniformity of the iterator along the two injections of each such sum.

Uniformity along the map forgetting the phase is not a field. It is the
one further premise of `iter_roundsStep_of_fold`. -/
structure PhaseSystem where
  iter : ∀ {X Y : C}, (X ⟶ Y ⨿ X) → (X ⟶ Y)
  fixpoint : ∀ {X Y : C} (f : X ⟶ Y ⨿ X), iter f = f ≫ coprod.desc (𝟙 Y) (iter f)
  naturality : ∀ {X Y Z : C} (f : X ⟶ Y ⨿ X) (g : Y ⟶ Z),
    iter f ≫ g = iter (f ≫ coprod.map g (𝟙 X))
  codiagonal : ∀ {X Y : C} (f : X ⟶ (Y ⨿ X) ⨿ X),
    iter (iter f) = iter (f ≫ coprod.desc (𝟙 (Y ⨿ X)) coprod.inr)
  obj : Nat → C
  inl (k : Nat) : obj 0 ⟶ obj (k + 1)
  inr (k : Nat) : obj k ⟶ obj (k + 1)
  desc (k : Nat) {T : C} : (obj 0 ⟶ T) → (obj k ⟶ T) → (obj (k + 1) ⟶ T)
  inl_desc : ∀ (k : Nat) {T : C} (u : obj 0 ⟶ T) (v : obj k ⟶ T), inl k ≫ desc k u v = u
  inr_desc : ∀ (k : Nat) {T : C} (u : obj 0 ⟶ T) (v : obj k ⟶ T), inr k ≫ desc k u v = v
  ext : ∀ (k : Nat) {T : C} {f g : obj (k + 1) ⟶ T},
    inl k ≫ f = inl k ≫ g → inr k ≫ f = inr k ≫ g → f = g
  uniform_inl : ∀ (k : Nat) {B : C} (f : obj 0 ⟶ B ⨿ obj 0) (g : obj (k + 1) ⟶ B ⨿ obj (k + 1)),
    f ≫ coprod.map (𝟙 B) (inl k) = inl k ≫ g → iter f = inl k ≫ iter g
  uniform_inr : ∀ (k : Nat) {B : C} (f : obj k ⟶ B ⨿ obj k) (g : obj (k + 1) ⟶ B ⨿ obj (k + 1)),
    f ≫ coprod.map (𝟙 B) (inr k) = inr k ≫ g → iter f = inr k ≫ iter g

/-- Forget the phase: every summand is the state. -/
def PhaseSystem.fold (S : PhaseSystem C) : (k : Nat) → (S.obj k ⟶ S.obj 0)
  | 0 => 𝟙 _
  | k + 1 => S.desc k (𝟙 _) (S.fold k)

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
