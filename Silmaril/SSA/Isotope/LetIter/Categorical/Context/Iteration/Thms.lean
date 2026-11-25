module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Iteration.Defs
public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Naturality.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.Context.Naturality

/-! # Contextual iteration and effectful exit continuations -/

public section

universe v₁ v₂ u₁ u₂

namespace Silmaril.Isotope.LetIter.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits CategoryTheory.PremonoidalCategory
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (caseWithContext contextualLoop duplicate retainLeft)

local notation "bindArrow" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind

local notation "fst" => CartesianMonoidalCategory.fst
local notation "snd" => CartesianMonoidalCategory.snd

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C)

section Distributive

variable [DistributiveFreydCategory J]

/-- Retaining a projected context through composition retains it at both steps. -/
theorem retainEnvironment_comp {E X Y Z : V} (p : X ⟶ E)
    (f : J.obj X ⟶ J.obj Y) (g : J.obj Y ⟶ J.obj Z) :
    retainEnvironment J p (f ≫ g) = retainEnvironment J p f ≫ retainLeft J g :=
  retainEnvironment_comp_proof J p f g

/-- Precomposition by a pure map changes how the context is projected. -/
@[reassoc] theorem retainEnvironment_pre {E X Y D : V} (q : D ⟶ X) (p : X ⟶ E)
    (f : J.obj X ⟶ J.obj Y) :
    J.map q ≫ retainEnvironment J p f = retainEnvironment J (q ≫ p) (J.map q ≫ f) :=
  retainEnvironment_pre_proof J q p f

/-- A bind with a projected context is composition after retaining that projection. -/
theorem bind_retainEnvironment {E X Y D : V} (p : X ⟶ E)
    (f : J.obj X ⟶ J.obj Y) (k : J.obj (E ⊗ Y) ⟶ J.obj D) :
    bindArrow J f (J.map (p ▷ Y) ≫ k) = retainEnvironment J p f ≫ k :=
  bind_retainEnvironment_proof J p f k

/-- Continue on the selected exit of a contextual case. -/
theorem caseWithContext_liftExit [FreydCategory.CentralUnit J] {E A B D Z : V}
    (central : IsCentral (J.map (duplicate E) ≫
      (Functor.StrongPremonoidal.tensorIso (J := J) E E).inv))
    (f : J.obj E ⟶ J.obj (A ⨿ B)) (k : J.obj (E ⊗ A) ⟶ J.obj D)
    (out : J.obj D ⟶ J.obj Z) (loop : J.obj (E ⊗ B) ⟶ J.obj Z) :
    caseWithContext J (bindArrow J f (liftExit J k)) (J.map (snd E D) ≫ out) loop =
      caseWithContext J f (k ≫ out) loop :=
  caseWithContext_liftExit_proof J central f k out loop

/-- Binding a pure payload and retaining its original context supplies both components. -/
theorem bind_purePayload {E B D : V} (k : J.obj (E ⊗ B) ⟶ J.obj D) :
    bindArrow J (J.map (snd E B)) (J.map (fst E B ▷ B) ≫ k) = k :=
  bind_purePayload_proof J k

end Distributive

section Iteration

variable [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J]

/-- Move an effectful exit continuation into the corresponding case branch of the loop body. -/
theorem contextualLoop_naturality [FreydCategory.CentralUnit J] {R A B D : V}
    (central : IsCentral (J.map (duplicate R) ≫
      (Functor.StrongPremonoidal.tensorIso (J := J) R R).inv))
    (shared : ∃ e : J.obj R ⊗ J.obj (R ⊗ A) = J.obj (R ⊗ (R ⊗ A)),
      Functor.StrongPremonoidal.tensorIso (J := J) R (R ⊗ A) = eqToIso e)
    (f : J.obj (R ⊗ A) ⟶ J.obj (B ⨿ A)) (k : J.obj (R ⊗ B) ⟶ J.obj D) :
    bindArrow J (contextualLoop J f) (J.map (fst R A ▷ B) ≫ k) =
      contextualLoop J (caseWithContext J f
        (J.map (fst R A ▷ B) ≫ k ≫ J.map (coprod.inl : D ⟶ D ⨿ A))
        (J.map (snd (R ⊗ A) A ≫ coprod.inr))) :=
  contextualLoop_naturality_proof J central shared f k

/-- An exit continuation composes after iteration of the retained-state body. -/
theorem contextualLoop_liftExit [FreydCategory.CentralUnit J] {E A B D : V}
    (central : IsCentral (J.map (duplicate E) ≫
      (Functor.StrongPremonoidal.tensorIso (J := J) E E).inv))
    (body : J.obj (E ⊗ A) ⟶ J.obj (B ⨿ A)) (k : J.obj (E ⊗ B) ⟶ J.obj D) :
    contextualLoop J (retainEnvironment J (fst E A) body ≫ liftExit J k) =
      iterate (contextualStep J body) ≫ k :=
  contextualLoop_liftExit_proof J central body k

/-- Retaining the context through a loop agrees with iteration on retained states. -/
theorem contextualLoop_retain {E A B : V}
    (central : IsCentral (J.map (duplicate E) ≫
      (Functor.StrongPremonoidal.tensorIso (J := J) E E).inv))
    (shared : ∃ e : J.obj E ⊗ J.obj (E ⊗ A) = J.obj (E ⊗ (E ⊗ A)),
      Functor.StrongPremonoidal.tensorIso (J := J) E (E ⊗ A) = eqToIso e)
    (body : J.obj (E ⊗ A) ⟶ J.obj (B ⨿ A)) :
    retainEnvironment J (fst E A) (contextualLoop J body) = iterate (contextualStep J body) :=
  contextualLoop_retain_proof J central shared body

end Iteration

end Silmaril.Isotope.LetIter.Semantics.Categorical
