module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.Context.Naturality

/-! # Change of the pure environment in categorical LetIter combinators -/

public section

universe v₁ v₂ u₁ u₂

namespace Silmaril.Isotope.LetIter.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits CategoryTheory.PremonoidalCategory
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (caseWithContext contextualLoop)

local notation "bindArrow" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]

section Distributive

variable (J : V ⥤ C) [DistributiveFreydCategory J]

/-- Changing the pure input environment commutes with contextual binding. -/
theorem bind_pre_map {D E A B : V} (k : D ⟶ E)
    (f : J.obj E ⟶ J.obj A) (g : J.obj (E ⊗ A) ⟶ J.obj B) :
    bindArrow J (J.map k ≫ f) (J.map (k ▷ A) ≫ g) = J.map k ≫ bindArrow J f g :=
  bind_pre_map_proof J k f g

/-- Changing the pure input environment commutes with sequential pairing. -/
theorem pair_pre_map {D E A B : V} (k : D ⟶ E)
    (f : J.obj E ⟶ J.obj A) (g : J.obj E ⟶ J.obj B) :
    Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.pair J
      (J.map k ≫ f) (J.map k ≫ g) =
    J.map k ≫ Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.pair J f g :=
  pair_pre_map_proof J k f g

/-- Changing the pure input environment commutes with contextual case analysis. -/
theorem case_pre_map {D E A B X : V} (k : D ⟶ E)
    (f : J.obj E ⟶ J.obj (A ⨿ B))
    (left : J.obj (E ⊗ A) ⟶ J.obj X) (right : J.obj (E ⊗ B) ⟶ J.obj X) :
    caseWithContext J (J.map k ≫ f) (J.map (k ▷ A) ≫ left) (J.map (k ▷ B) ≫ right) =
      J.map k ≫ caseWithContext J f left right :=
  case_pre_map_proof J k f left right

/-- Bind the scrutinee first, then perform contextual case analysis on its value. -/
theorem case_bind_value {E P A B X : V} (f : J.obj E ⟶ J.obj P)
    (p : P ⟶ A ⨿ B) (l : J.obj (E ⊗ A) ⟶ J.obj X) (r : J.obj (E ⊗ B) ⟶ J.obj X) :
    caseWithContext J (f ≫ J.map p) l r =
      bindArrow J f (caseWithContext J (J.map (CartesianMonoidalCategory.snd E P ≫ p))
        (J.map (CartesianMonoidalCategory.fst E P ▷ A) ≫ l) (J.map (CartesianMonoidalCategory.fst E P ▷ B) ≫ r)) :=
  case_bind_value_proof J f p l r

end Distributive

section Iteration

variable [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]

/-- Changing the pure input environment commutes with contextual iteration. -/
theorem contextualLoop_pre_map {D E A B : V} (k : D ⟶ E)
    (f : J.obj (E ⊗ A) ⟶ J.obj (B ⨿ A)) :
    contextualLoop J (J.map (k ▷ A) ≫ f) = J.map (k ▷ A) ≫ contextualLoop J f :=
  contextualLoop_pre_map_proof J k f

/-- Unfold contextual iteration as a case on one step of its body. -/
theorem contextualLoop_fixpoint {R A B : V} (f : J.obj (R ⊗ A) ⟶ J.obj (B ⨿ A)) :
    contextualLoop J f = caseWithContext J f
      (J.map (CartesianMonoidalCategory.snd (R ⊗ A) B)) (J.map (CartesianMonoidalCategory.fst R A ▷ A) ≫ contextualLoop J f) :=
  contextualLoop_fixpoint_proof J f

end Iteration

end Silmaril.Isotope.LetIter.Semantics.Categorical
