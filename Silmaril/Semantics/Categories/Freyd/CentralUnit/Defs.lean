module

public import Silmaril.Raw.Semantics.Categories.Freyd.Basic

/-! # Central unit comparisons for Freyd categories -/

public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.FreydCategory

/-- The chosen Freyd unit comparison commutes with arbitrary computations.

In the shared-unit presentation the comparison is the identity. This refinement
allows any central comparison and applies to a particular chosen Freyd structure. -/
class CentralUnit {V : Type u₁} {C : Type u₂}
    [Category.{v₁} V] [Category.{v₂} C]
    [CartesianMonoidalCategory V] [SymmetricCategory V]
    [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
    (J : V ⥤ C) [FreydCategory J] : Prop where
  unit_central : PremonoidalCategory.IsCentral (Functor.StrongPremonoidal.unitIso (J := J)).hom

end CategoryTheory.FreydCategory
