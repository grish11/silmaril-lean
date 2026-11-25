module

public import Silmaril.Semantics.Categories.Freyd.CentralUnit.Defs
public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Thms

/-! # Context duplication in plain Freyd models with a central unit -/

@[expose] public section

namespace Silmaril.Isotope.LetIter.Semantics.Categorical

open CategoryTheory CategoryTheory.PremonoidalCategory
open CategoryTheory.CartesianMonoidalCategory (fst)
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (duplicate)

local notation "bindArrow" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind

/-- Centrality of transported diagonals in small Freyd models with a central unit. -/
def CentralUnitTransportedDiagonals : Prop :=
  ∀ {V C : Type 1} [Category.{0} V] [Category.{0} C]
    [CartesianMonoidalCategory V] [SymmetricCategory V]
    [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
    (J : V ⥤ C) [FreydCategory J] [FreydCategory.CentralUnit J] (E : V),
    IsCentral (J.map (duplicate E) ≫ (Functor.StrongPremonoidal.tensorIso (J := J) E E).inv)

/-- Contextual bind associativity in small Freyd models with a central unit. -/
def CentralUnitContextualBindAssoc : Prop :=
  ∀ {V C : Type 1} [Category.{0} V] [Category.{0} C]
    [CartesianMonoidalCategory V] [SymmetricCategory V]
    [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
    (J : V ⥤ C) [FreydCategory J] [FreydCategory.CentralUnit J]
    {E A B D : V} (f : J.obj E ⟶ J.obj A)
    (g : J.obj (E ⊗ A) ⟶ J.obj B) (k : J.obj (E ⊗ B) ⟶ J.obj D),
    bindArrow J (bindArrow J f g) k =
      bindArrow J f (bindArrow J g (J.map (fst E A ▷ B) ≫ k))

end Silmaril.Isotope.LetIter.Semantics.Categorical
