module

public import Silmaril.SSA.RVSDG.Categorical.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Defs

public section

namespace Silmaril.SSA.RVSDG.Categorical.Proofs

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory (lift)
open CategoryTheory.PremonoidalCategory (leftTensor)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (bind duplicate)
open scoped MonoidalCategory

universe d h c k
variable {D : Type d} {C : Type c} [Category.{h} D] [Category.{k} C]
  [CartesianMonoidalCategory D] (J : D ⥤ C)

theorem bind_map [SymmetricCategory D] [PremonoidalCategory C]
    [SymmetricPremonoidalCategory C] [FreydCategory J] {R A B : D}
    (f : R ⟶ A) (g : R ⊗ A ⟶ B) :
    bind J (J.map f) (J.map g) = J.map (lift (𝟙 R) f ≫ g) := by
  unfold Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind
    Isotope.LetIter.ProofRelevant.Semantics.Categorical.extend duplicate
  rw [leftTensor]
  simp only [PremonoidalCategory.id_whiskerRight, Category.id_comp, Category.assoc]
  rw [← Category.assoc (J.obj R ◁ J.map f), Functor.StrongPremonoidal.tensor_naturality_right]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp]
  congr 1
  simp

theorem dispatch_map [PreservesFiniteCoproducts J] (sel : Selectors D)
    {n : Nat} {X Y : D} (arms : Fin n → (X ⟶ Y)) :
    (isColimitOfPreserves J (sel.colimit n X)).desc (J.mapCocone (Cofan.mk Y arms)) =
      J.map (dispatch sel arms) :=
  preserves_desc_mapCocone J _ _ _ (sel.colimit n X)

end Silmaril.SSA.RVSDG.Categorical.Proofs
