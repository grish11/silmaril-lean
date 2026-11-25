module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms
public import Silmaril.Semantics.Categories.Freyd.CentralUnit.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Iteration.Thms

/-! # Continuations on outward exits of a LambdaSSA dispatcher -/

public section

universe v₁ v₂ u₁ u₂

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

export Silmaril.Isotope.LetIter.Semantics.Categorical
  (retainEnvironment routeEnvironment liftExit retainEnvironment_comp
    retainEnvironment_pre retainEnvironment_pre_assoc bind_retainEnvironment)

open CategoryTheory CategoryTheory.Limits CategoryTheory.PremonoidalCategory
open Silmaril.Isotope.LetIter.Semantics.Categorical
  (caseWithContext_liftExit contextualLoop_liftExit bind_purePayload bind_case_capture contextualLoop_retain)
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (caseWithContext contextualLoop duplicate)

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

variable [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J]

theorem caseLoop_exitContinuation [FreydCategory.CentralUnit J] {E A B D : V}
    (central : IsCentral (J.map (duplicate E) ≫
      (Functor.StrongPremonoidal.tensorIso (J := J) E E).inv))
    (shared : ∃ e : J.obj E ⊗ J.obj (E ⊗ A) = J.obj (E ⊗ (E ⊗ A)),
      Functor.StrongPremonoidal.tensorIso (J := J) E (E ⊗ A) = eqToIso e)
    (entry : J.obj E ⟶ J.obj (B ⨿ A))
    (body : J.obj (E ⊗ A) ⟶ J.obj (B ⨿ A)) (k : J.obj (E ⊗ B) ⟶ J.obj D) :
    caseWithContext J (bindArrow J entry (liftExit J k)) (J.map (snd E D))
        (contextualLoop J (retainEnvironment J (fst E A) body ≫ liftExit J k)) =
      bindArrow J (caseWithContext J entry (J.map (snd E B)) (contextualLoop J body)) k := by
  have h := caseWithContext_liftExit J central entry k (𝟙 (J.obj D))
    (contextualLoop J (retainEnvironment J (fst E A) body ≫ liftExit J k))
  simp only [Category.comp_id] at h
  rw [h, contextualLoop_liftExit J central, bind_case_capture J central, bind_purePayload,
    bind_retainEnvironment, contextualLoop_retain J central shared]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
