module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Thms

public section

namespace Silmaril.Isotope.LetIter.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits CategoryTheory.PremonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (duplicate)
open CategoryTheory.Functor.StrongPremonoidal
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (extend)

universe v₁ v₂ u₁ u₂

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  (J : V ⥤ C)

/-- Postcomposition by a pure arrow can run after retaining the environment. -/
theorem extend_postmap_proof [FreydCategory J] {R A B : V} (f : J.obj R ⟶ J.obj A) (p : A ⟶ B) :
    extend J (f ≫ J.map p) = extend J f ≫ J.map (R ◁ p) := by
  simp only [extend, leftTensor, id_whiskerRight, Category.id_comp,
    whiskerLeft_comp, Category.assoc]
  rw [tensor_naturality_right (J := J)]

theorem extend_map_proof [FreydCategory J] {R A : V} (p : R ⟶ A) :
    extend J (J.map p) = J.map (lift (𝟙 R) p) := by
  simp only [extend, leftTensor, id_whiskerRight, Category.id_comp]
  rw [tensor_naturality_right (J := J), Iso.inv_hom_id_assoc, ← J.map_comp]
  congr 1
  apply hom_ext
  · simp [duplicate]
  · simp [duplicate]

end Silmaril.Isotope.LetIter.Semantics.Categorical
