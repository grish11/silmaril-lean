module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralSquareFactorization

/-! # Factoring a commuting iteration square through a split state map -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton

open CategoryTheory CategoryTheory.Limits
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

universe u v
variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
  {A D E B : C} (h : A ⟶ D) (k : D ⟶ E)
  (f : A ⟶ B ⨿ A) (g : E ⟶ B ⨿ E)
  (square : f ≫ coprod.map (𝟙 B) (h ≫ k) = (h ≫ k) ≫ g)

include square in
/-- For a split first map, a unique intermediate iteration step exists exactly
when the source transition followed by the first map is invariant under
resetting the input along its section. That step is forced by the section. -/
theorem intermediate_iff_of_section (s : D ⟶ A) (hs : s ≫ h = 𝟙 D) :
    (∃! m : D ⟶ B ⨿ D,
      f ≫ coprod.map (𝟙 B) h = h ≫ m ∧ m ≫ coprod.map (𝟙 B) k = k ≫ g) ↔
    f ≫ coprod.map (𝟙 B) h = (h ≫ s) ≫ f ≫ coprod.map (𝟙 B) h :=
  StructuralSquareFactorization.intermediate_iff_of_section h k f g square s hs

include square in
/-- A split first map and a split monic second map always admit a unique
intermediate step for a commuting composite square. -/
theorem intermediate_of_section_of_retraction (s : D ⟶ A) (hs : s ≫ h = 𝟙 D)
    (r : E ⟶ D) (hr : k ≫ r = 𝟙 D) :
    ∃! m : D ⟶ B ⨿ D,
      f ≫ coprod.map (𝟙 B) h = h ≫ m ∧ m ≫ coprod.map (𝟙 B) k = k ≫ g :=
  StructuralSquareFactorization.intermediate_of_section_of_retraction h k f g square s hs r hr

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
