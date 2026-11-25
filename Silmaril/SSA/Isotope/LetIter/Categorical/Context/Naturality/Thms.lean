module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.Context.Naturality

/-! # Change of the pure environment in categorical LetIter combinators -/

public section

universe v₁ v₂ u₁ u₂

namespace Silmaril.Isotope.LetIter.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits CategoryTheory.PremonoidalCategory
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (caseWithContext contextualLoop duplicate extend retainLeft)

local notation "bindArrow" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind

local notation "fst" => CartesianMonoidalCategory.fst
local notation "lift" => CartesianMonoidalCategory.lift

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

local notation "tIso" => Functor.StrongPremonoidal.tensorIso (J := J)

/-- Retaining a duplicated value context commutes with an arbitrary computation when the transported diagonal is central. -/
theorem retainLeft_copy {E A B : V} (f : J.obj A ⟶ J.obj B)
    (central : IsCentral (J.map (duplicate E) ≫ (tIso E E).inv)) :
    J.map ((duplicate E ▷ A) ≫ (α_ E E A).hom) ≫
      retainLeft J (R := E) (retainLeft J (R := E) f) =
    retainLeft J (R := E) f ≫ J.map ((duplicate E ▷ B) ≫ (α_ E E B).hom) :=
  retainLeft_copy_proof J f central

omit [SymmetricCategory V] [HasFiniteCoproducts V] [DistributiveTensor V] in
/-- The Cartesian diagonal and associator put one copy of the context beside the unchanged input pair. -/
theorem copyValue (E A : V) :
    (duplicate E ▷ A) ≫ (α_ E E A).hom = lift (fst E A) (𝟙 (E ⊗ A)) :=
  copyValue_proof E A

/-- Retain an extra copy of the context through a computation that already retains its input. -/
@[reassoc] theorem extend_capture {E A : V} (f : J.obj E ⟶ J.obj A)
    (central : IsCentral (J.map (duplicate E) ≫ (tIso E E).inv)) :
    J.map (duplicate E) ≫ retainLeft J (R := E) (extend J f) =
      extend J f ≫ J.map (lift (fst E A) (𝟙 (E ⊗ A))) :=
  extend_capture_proof J f central

/-- Reassociate contextual binds under centrality of the transported value diagonal. -/
theorem bind_assoc_capture {E A B D : V}
    (central : IsCentral (J.map (duplicate E) ≫ (tIso E E).inv))
    (f : J.obj E ⟶ J.obj A) (g : J.obj (E ⊗ A) ⟶ J.obj B)
    (k : J.obj (E ⊗ B) ⟶ J.obj D) :
    bindArrow J (bindArrow J f g) k =
      bindArrow J f (bindArrow J g (J.map (fst E A ▷ B) ≫ k)) :=
  bind_assoc_capture_proof J central f g k

/-- Reassociate contextual binds through an explicit reindexing of the intermediate environment. -/
theorem bind_assoc_reindex {E A X B D : V}
    (central : IsCentral (J.map (duplicate E) ≫ (tIso E E).inv))
    (f : J.obj E ⟶ J.obj A) (p : E ⊗ A ⟶ X)
    (g : J.obj X ⟶ J.obj B) (q : X ⟶ E) (hq : p ≫ q = fst E A)
    (k : J.obj (E ⊗ B) ⟶ J.obj D) :
    bindArrow J (bindArrow J f (J.map p ≫ g)) k =
      bindArrow J f (J.map p ≫ bindArrow J g (J.map (q ▷ B) ≫ k)) :=
  bind_assoc_reindex_proof J central f p g q hq k

/-- Distribute a continuation into both branches of a contextual case. -/
theorem bind_case_capture {E A B X Y : V}
    (central : IsCentral (J.map (duplicate E) ≫ (tIso E E).inv))
    (scrutinee : J.obj E ⟶ J.obj (A ⨿ B))
    (left : J.obj (E ⊗ A) ⟶ J.obj X) (right : J.obj (E ⊗ B) ⟶ J.obj X)
    (k : J.obj (E ⊗ X) ⟶ J.obj Y) :
    bindArrow J (caseWithContext J scrutinee left right) k =
      caseWithContext J scrutinee
        (bindArrow J left (J.map (fst E A ▷ X) ≫ k))
        (bindArrow J right (J.map (fst E B ▷ X) ≫ k)) :=
  bind_case_capture_proof J central scrutinee left right k

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
