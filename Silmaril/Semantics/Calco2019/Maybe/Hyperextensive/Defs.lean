module

public import Silmaril.Semantics.Calco2019.Maybe.LoopDecomposition.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-! # Countable coproducts for the hyperextensive case of §1.3

This formulates the three conditions of Adámek, Börger, Milius and Velebil,
*Iterative algebras: How iterative are they?*, Definition 2.5.
-/

@[expose] public section

universe u v

namespace Silmaril.Calco2019.Maybe

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

/-- A coproduct injection together with its complementary leg. -/
structure Complement {A X : C} (f : A ⟶ X) where
  other : C
  incl : other ⟶ X
  colimit : IsColimit (BinaryCofan.mk f incl)

/-- A common factor through two inclusions must have an initial domain. -/
def Disjoint {A B X : C} (f : A ⟶ X) (g : B ⟶ X) : Prop :=
  ∀ ⦃D : C⦄ (p : D ⟶ A) (q : D ⟶ B), p ≫ f = q ≫ g → Nonempty (IsInitial D)

/-- Pulling back each injection yields another coproduct over the new domain. -/
structure PullbackCofan {I : Type} {F : I → C} (c : Cofan F) {X : C} (f : X ⟶ c.pt) where
  obj : I → C
  incl (i : I) : obj i ⟶ X
  map (i : I) : obj i ⟶ F i
  pullback (i : I) : IsPullback (incl i) (map i) f (c.inj i)
  colimit : IsColimit (Cofan.mk X incl)

/-- Countable coproducts are disjoint and universal, and countable unions of
pairwise disjoint complemented subobjects are complemented. -/
class Hyperextensive (C : Type u) [Category.{v} C] : Prop where
  [hasCountableCoproducts : HasCountableCoproducts C]
  mono {I : Type} [Countable I] {F : I → C} (c : Cofan F) (hc : IsColimit c)
    (i : I) : Mono (c.inj i)
  disjoint {I : Type} [Countable I] {F : I → C} (c : Cofan F) (hc : IsColimit c) :
    Pairwise (fun i j => Disjoint (c.inj i) (c.inj j))
  universal {I : Type} [Countable I] {F : I → C} (c : Cofan F) (hc : IsColimit c)
    {X : C} (f : X ⟶ c.pt) : Nonempty (PullbackCofan c f)
  union {F : ℕ → C} {X : C} (f : ∀ n, F n ⟶ X) :
    (∀ n, Nonempty (Complement (f n))) → Pairwise (fun i j => Disjoint (f i) (f j)) →
    Nonempty (Complement (Sigma.desc f))

attribute [instance] Hyperextensive.hasCountableCoproducts

end Silmaril.Calco2019.Maybe
