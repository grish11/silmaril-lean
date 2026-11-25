module

public import Silmaril.Semantics.Categories.Freyd.CentralUnit.Defs
public import Silmaril.Raw.Semantics.Categories.Monad.Kleisli
import Silmaril.Proofs.Semantics.Categories.Freyd.CentralUnit

/-! # Projection naturality with a central Freyd unit comparison -/

public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.FreydCategory

open PremonoidalCategory
open CartesianMonoidalCategory (snd)
open scoped MonoidalCategory

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  (J : V ⥤ C) [FreydCategory J]

/-- The identity comparison of a shared unit satisfies the central-unit boundary. -/
theorem CentralUnit.of_unitIso_eqToIso (h : 𝟙_ C = J.obj (𝟙_ V))
    (comparison : Functor.StrongPremonoidal.unitIso (J := J) = eqToIso h) :
    CentralUnit J := by
  constructor
  rw [comparison]
  exact Eq.recOn h (isCentral_id (𝟙_ C))

/-- Discarding the fixed left input commutes with a computation on the right
if the chosen unit comparison is central. -/
theorem whiskerLeft_snd_of_unit_central
    (h : IsCentral (Functor.StrongPremonoidal.unitIso (J := J)).hom) (R : V) {A B : V}
    (f : J.obj A ⟶ J.obj B) :
    (Functor.StrongPremonoidal.tensorIso (J := J) R A).inv ≫
      J.obj R ◁ f ≫ (Functor.StrongPremonoidal.tensorIso (J := J) R B).hom ≫
        J.map (snd R B) = J.map (snd R A) ≫ f :=
  whiskerLeft_snd_proof J h R f

/-- Discarding the fixed left input commutes with a computation on the right. -/
theorem whiskerLeft_snd [CentralUnit J] (R : V) {A B : V} (f : J.obj A ⟶ J.obj B) :
    (Functor.StrongPremonoidal.tensorIso (J := J) R A).inv ≫
      J.obj R ◁ f ≫ (Functor.StrongPremonoidal.tensorIso (J := J) R B).hom ≫
        J.map (snd R B) = J.map (snd R A) ≫ f :=
  whiskerLeft_snd_of_unit_central J (CentralUnit.unit_central (J := J)) R f

/-- Centrality of the unit comparison is equivalent to naturality of the mapped
second projection under right-slot computation at the value unit. In particular,
naturality for every fixed left argument requires this centrality. -/
theorem centralUnit_iff_whiskerLeft_snd_at_unit :
    CentralUnit J ↔
      ∀ {A B : V} (f : J.obj A ⟶ J.obj B),
        (Functor.StrongPremonoidal.tensorIso (J := J) (𝟙_ V) A).inv ≫
          J.obj (𝟙_ V) ◁ f ≫ (Functor.StrongPremonoidal.tensorIso (J := J) (𝟙_ V) B).hom ≫
            J.map (snd (𝟙_ V) B) = J.map (snd (𝟙_ V) A) ≫ f :=
  ⟨fun h {A B} f => whiskerLeft_snd_of_unit_central J h.unit_central (𝟙_ V) (A := A) (B := B) f,
    centralUnit_of_whiskerLeft_snd_proof J⟩

end CategoryTheory.FreydCategory

namespace CategoryTheory.Kleisli

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [SymmetricCategory V]

/-- The canonical Kleisli inclusion of a strong monad uses the identity unit comparison. -/
instance toKleisliCentralUnit (T : Monad V) [T.Strong] :
    FreydCategory.CentralUnit (Kleisli.Adjunction.toKleisli T) :=
  FreydCategory.CentralUnit.of_unitIso_eqToIso _ rfl rfl

end CategoryTheory.Kleisli
