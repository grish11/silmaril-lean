module

public import Silmaril.SSA.Isotope.LetParIter.Categorical.Defs

/-! # Additional semantic laws for the Par generators -/

@[expose] public section

namespace Silmaril.Isotope.LetParIter.Categorical

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped MonoidalCategory
open LetIter.ProofRelevant.Semantics.Categorical (extend caseWithContext)

universe v₁ v₂ u₁ u₂

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [∀ X Y : C, Preorder (X ⟶ Y)]
  (J : V ⥤ C) [DistributiveFreydCategory J] (P : FreydCategory.OrderedParallel J)

/-- Supply each returned value with the retained input, in branch order. -/
noncomputable def splitContext (R A B : V) : R ⊗ (A ⊗ B) ⟶ (R ⊗ A) ⊗ (R ⊗ B) :=
  lift (lift (fst _ _) (snd _ _ ≫ fst _ _)) (lift (fst _ _) (snd _ _ ≫ snd _ _))

/-- Semantic diagrams for copying the retained values through two effectful branches and
commuting a case with parallel when its scrutinee is a value map. These diagrams quantify
over arrows and are independent of the syntax, its typing and its equation relation. -/
structure Laws : Prop where
  extend_par {R A B : V} (f : J.obj R ⟶ J.obj A) (g : J.obj R ⟶ J.obj B) :
    P.par (extend J f) (extend J g) = extend J (P.par f g) ≫ J.map (splitContext R A B)
  case_left {R A B X Y : V} (s : R ⟶ A ⨿ B)
      (l : J.obj (R ⊗ A) ⟶ J.obj X) (r : J.obj (R ⊗ B) ⟶ J.obj X)
      (g : J.obj R ⟶ J.obj Y) :
    P.par (caseWithContext J (J.map s) l r) g =
      caseWithContext J (J.map s)
        (P.par l (J.map (fst R A) ≫ g)) (P.par r (J.map (fst R B) ≫ g))

end Silmaril.Isotope.LetParIter.Categorical
