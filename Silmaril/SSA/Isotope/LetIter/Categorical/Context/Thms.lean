module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.Context

/-! # Context retention in categorical LetIter -/

public section

namespace Silmaril.Isotope.LetIter.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (extend)
open Silmaril.Isotope.LetIter.LocallyNameless (Derivation Tm)

universe v₁ v₂ u₁ u₂

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  (J : V ⥤ C)

/-- Postcomposition by a pure arrow can run after retaining the environment. -/
theorem extend_postmap [FreydCategory J] {R A B : V} (f : J.obj R ⟶ J.obj A) (p : A ⟶ B) :
    extend J (f ≫ J.map p) = extend J f ≫ J.map (R ◁ p) :=
  extend_postmap_proof J f p

/-- The context-retaining form of a value arrow is its Cartesian pairing with identity. -/
theorem extend_map [FreydCategory J] {R A : V} (p : R ⟶ A) :
    extend J (J.map p) = J.map (CartesianMonoidalCategory.lift (𝟙 R) p) :=
  extend_map_proof J p

end Silmaril.Isotope.LetIter.Semantics.Categorical
