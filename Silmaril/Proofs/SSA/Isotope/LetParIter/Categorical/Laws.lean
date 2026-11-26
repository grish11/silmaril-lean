module

public import Silmaril.SSA.Isotope.LetParIter.Categorical.Laws.Defs
public import Silmaril.SSA.Isotope.LetIter.Categorical.Parallel.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Case.Thms

public section

namespace Silmaril.Isotope.LetParIter.Categorical

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped MonoidalCategory
open LetIter.ProofRelevant.Semantics.Categorical (extend caseWithContext)
open LetIter.Semantics.Categorical (par_id_left_eq_extend case_postcomp)

universe v₁ v₂ u₁ u₂

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [∀ X Y : C, Preorder (X ⟶ Y)]
  (J : V ⥤ C)

theorem extend_snd_proof [FreydCategory J] (P : FreydCategory.OrderedParallel J)
    {R A : V} (f : J.obj R ⟶ J.obj A) :
    extend J f ≫ J.map (snd R A) = f := by
  have h := P.par_postmap (𝟙 (J.obj R)) f (toUnit R) (𝟙 A)
  simp only [Category.id_comp] at h
  rw [← par_id_left_eq_extend P f, ← whiskerRight_toUnit_comp_leftUnitor_hom,
    J.map_comp, ← Category.assoc, ← MonoidalCategory.tensorHom_id, h, P.par_unit_left]
  rw [J.map_id, Category.comp_id]

variable [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [DistributiveFreydCategory J] (P : FreydCategory.OrderedParallel J) (L : Laws J P)

include L

theorem par_context_maps_proof {R A B X Y : V}
    (f : J.obj R ⟶ J.obj A) (g : J.obj R ⟶ J.obj B)
    (u : R ⊗ A ⟶ X) (v : R ⊗ B ⟶ Y) :
    P.par (extend J f ≫ J.map u) (extend J g ≫ J.map v) =
      extend J (P.par f g) ≫ J.map (splitContext R A B ≫ (u ⊗ₘ v)) := by
  rw [← P.par_postmap, L.extend_par, J.map_comp, Category.assoc]

theorem par_case_right_proof {R A B X Y : V} (s : R ⟶ A ⨿ B)
    (l : J.obj (R ⊗ A) ⟶ J.obj X) (r : J.obj (R ⊗ B) ⟶ J.obj X)
    (g : J.obj R ⟶ J.obj Y) :
    P.par g (caseWithContext J (J.map s) l r) =
      caseWithContext J (J.map s)
        (P.par (J.map (fst R A) ≫ g) l) (P.par (J.map (fst R B) ≫ g) r) := by
  apply (cancel_mono (J.map (BraidedCategory.braiding Y X).hom)).1
  rw [P.par_swap, case_postcomp, P.par_swap, P.par_swap, L.case_left]

end Silmaril.Isotope.LetParIter.Categorical
