module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Thms

public section

namespace Silmaril.Isotope.LetIter.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits CategoryTheory.PremonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (duplicate)
open CategoryTheory.Functor.StrongPremonoidal
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (extend retainLeft)

universe v₁ v₂ u₁ u₂

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  (J : V ⥤ C)

@[reassoc] theorem retainLeft_pre_map_proof {D E A B : V} [FreydCategory J] (k : D ⟶ E)
    (f : J.obj A ⟶ J.obj B) :
    J.map (k ▷ A) ≫ retainLeft J (R := E) f =
      retainLeft J (R := D) f ≫ J.map (k ▷ B) := by
  let t := Functor.StrongPremonoidal.tensorIso (J := J)
  apply (cancel_epi (t D A).hom).mp
  have exchange := (FreydCategory.image_central J k).1 f
  unfold leftTensor rightTensor at exchange
  simp only [retainLeft, leftTensor, id_whiskerRight, Category.id_comp, Category.assoc]
  rw [← Category.assoc (t D A).hom, ← Functor.StrongPremonoidal.tensor_naturality_left]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Functor.StrongPremonoidal.tensor_naturality_left, ← Category.assoc
    (J.obj D ◁ f), ← exchange]
  simp only [t, Category.assoc, Iso.hom_inv_id_assoc]

theorem extend_comp_proof [FreydCategory J] {R A B : V}
    (f : J.obj R ⟶ J.obj A) (g : J.obj A ⟶ J.obj B) :
    extend J (f ≫ g) = extend J f ≫ retainLeft J g := by
  simp [extend, retainLeft, leftTensor, whiskerLeft_comp]

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
