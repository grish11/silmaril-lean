module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Thms
public import Silmaril.Semantics.Categories.Freyd.CentralUnit.Defs

/-! # Retained environments in contextual iteration -/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace Silmaril.Isotope.LetIter.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits CategoryTheory.PremonoidalCategory
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (retainLeft splitMapCoprod)

local notation "fst" => CartesianMonoidalCategory.fst
local notation "snd" => CartesianMonoidalCategory.snd
local notation "lift" => CartesianMonoidalCategory.lift

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C)

variable [DistributiveFreydCategory J]

/-- Run a computation while retaining a pure projection of its source. -/
noncomputable def retainEnvironment {E X Y : V} (p : X ⟶ E) (f : J.obj X ⟶ J.obj Y) :
    J.obj X ⟶ J.obj (E ⊗ Y) :=
  J.map (lift p (𝟙 X)) ≫ retainLeft J f

/-- Route the retained context into the selected coproduct branch. -/
noncomputable def routeEnvironment (E A B : V) :
    J.obj (E ⊗ (A ⨿ B)) ⟶ J.obj (E ⊗ A) ⨿ J.obj (E ⊗ B) :=
  J.map (DistributiveTensor.leftIso E A B).inv ≫ splitMapCoprod J (E ⊗ A) (E ⊗ B)

/-- Apply an exit continuation while preserving the recurrence summand. -/
noncomputable def liftExit {E A B D : V}
    (k : J.obj (E ⊗ A) ⟶ J.obj D) :
    J.obj (E ⊗ (A ⨿ B)) ⟶ J.obj (D ⨿ B) :=
  routeEnvironment J E A B ≫
    coprod.desc (k ≫ J.map (coprod.inl : D ⟶ D ⨿ B)) (J.map (snd E B ≫ coprod.inr))

/-- One loop step keeps the context in both the exit and recurrence summands. -/
noncomputable def contextualStep {E A B : V}
    (body : J.obj (E ⊗ A) ⟶ J.obj (B ⨿ A)) :
    J.obj (E ⊗ A) ⟶ J.obj (E ⊗ B) ⨿ J.obj (E ⊗ A) :=
  retainEnvironment J (fst E A) body ≫ routeEnvironment J E B A

end Silmaril.Isotope.LetIter.Semantics.Categorical
