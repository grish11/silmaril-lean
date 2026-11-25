module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.Context

/-! # Context retention in categorical LetIter -/

public section

namespace Silmaril.Isotope.LetIter.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (extend retainLeft)
open Silmaril.Isotope.LetIter.LocallyNameless (Derivation Tm)

universe v₁ v₂ u₁ u₂

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  (J : V ⥤ C)

/-- Changing the retained context by a value map commutes with running the computation. -/
@[reassoc] theorem retainLeft_pre_map {D E A B : V} [FreydCategory J] (k : D ⟶ E)
    (f : J.obj A ⟶ J.obj B) :
    J.map (k ▷ A) ≫ retainLeft J (R := E) f =
      retainLeft J (R := D) f ≫ J.map (k ▷ B) :=
  retainLeft_pre_map_proof J k f

/-- Retain the original context through two consecutive computations. -/
theorem extend_comp [FreydCategory J] {R A B : V}
    (f : J.obj R ⟶ J.obj A) (g : J.obj A ⟶ J.obj B) :
    extend J (f ≫ g) = extend J f ≫ retainLeft J g :=
  extend_comp_proof J f g

/-- Postcomposition by a pure arrow can run after retaining the environment. -/
theorem extend_postmap [FreydCategory J] {R A B : V} (f : J.obj R ⟶ J.obj A) (p : A ⟶ B) :
    extend J (f ≫ J.map p) = extend J f ≫ J.map (R ◁ p) :=
  extend_postmap_proof J f p

/-- The context-retaining form of a value arrow is its Cartesian pairing with identity. -/
theorem extend_map [FreydCategory J] {R A : V} (p : R ⟶ A) :
    extend J (J.map p) = J.map (CartesianMonoidalCategory.lift (𝟙 R) p) :=
  extend_map_proof J p

end Silmaril.Isotope.LetIter.Semantics.Categorical
