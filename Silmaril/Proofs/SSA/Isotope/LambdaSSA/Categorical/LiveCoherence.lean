module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.Live.Defs
import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Iteration.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Singleton.Thms

/-! # Compare contextual dispatchers using a common factored transition -/

public section

universe u₁ u₂ v₁ v₂

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.LiveCoherence

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open CartesianMonoidalCategory (fst snd)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (caseWithContext contextualLoop extend retainLeft splitMapCoprod)
open Silmaril.Isotope.LetIter.Semantics.Categorical
  (contextualStep extend_postmap retainEnvironment retainEnvironment_pre retainEnvironment_comp routeEnvironment)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open SingletonDispatcher (route_inl route_inr)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C)

section Distributive

variable [DistributiveFreydCategory J]

private theorem route_state {E A B D : V} (h : A ⟶ D) :
    J.map (E ◁ coprod.map (𝟙 B) h) ≫ routeEnvironment J E B D =
      routeEnvironment J E B A ≫ coprod.map (𝟙 (J.obj (E ⊗ B))) (J.map (E ◁ h)) := by
  let route := routeEnvironment J E B A
  have : IsIso route := by
    dsimp only [route, routeEnvironment, splitMapCoprod]
    infer_instance
  have left : J.map (E ◁ (coprod.inl : B ⟶ B ⨿ A)) ≫ route = coprod.inl := route_inl J
  have right : J.map (E ◁ (coprod.inr : A ⟶ B ⨿ A)) ≫ route = coprod.inr := route_inr J
  have left_inv : coprod.inl ≫ inv route = J.map (E ◁ (coprod.inl : B ⟶ B ⨿ A)) := by
    rw [← left, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have right_inv : coprod.inr ≫ inv route = J.map (E ◁ (coprod.inr : A ⟶ B ⨿ A)) := by
    rw [← right, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  change _ = route ≫ _
  apply (cancel_epi (inv route)).mp
  simp only [IsIso.inv_hom_id_assoc]
  apply coprod.hom_ext
  · rw [← Category.assoc, left_inv, ← J.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp,
      coprod.inl_map, Category.id_comp, route_inl J, coprod.inl_map, Category.id_comp]
  · rw [← Category.assoc, right_inv, ← J.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp,
      coprod.inr_map, MonoidalCategory.whiskerLeft_comp, J.map_comp_assoc, route_inr J, coprod.inr_map]

private theorem case_state {E A B D X : V} (h : A ⟶ D)
    (entry : J.obj E ⟶ J.obj (B ⨿ A))
    (out : J.obj (E ⊗ B) ⟶ J.obj X) (loop : J.obj (E ⊗ D) ⟶ J.obj X) :
    caseWithContext J (entry ≫ J.map (coprod.map (𝟙 B) h)) out loop =
      caseWithContext J entry out (J.map (E ◁ h) ≫ loop) := by
  have expand {S : V} (f : J.obj E ⟶ J.obj (B ⨿ S))
      (r : J.obj (E ⊗ S) ⟶ J.obj X) :
      caseWithContext J f out r = extend J f ≫ routeEnvironment J E B S ≫ coprod.desc out r := by
    simp only [caseWithContext, Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind,
      routeEnvironment, Category.assoc]
  rw [expand, expand]
  rw [extend_postmap, Category.assoc, ← Category.assoc (J.map _), route_state, Category.assoc,
    coprod.map_desc, Category.id_comp]

end Distributive

section Iteration

variable [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J]

private theorem step_pre {E A B D S : V} (h : A ⟶ D)
    (body : J.obj (E ⊗ D) ⟶ J.obj (B ⨿ S)) :
    retainEnvironment J (fst E A) (J.map (E ◁ h) ≫ body) =
      J.map (E ◁ h) ≫ retainEnvironment J (fst E D) body := by
  rw [retainEnvironment_pre, CartesianMonoidalCategory.whiskerLeft_fst]

private theorem step_post {E A B D S : V} (h : A ⟶ D)
    (body : J.obj (E ⊗ S) ⟶ J.obj (B ⨿ A)) :
    retainEnvironment J (fst E S) (body ≫ J.map (coprod.map (𝟙 B) h)) ≫
        routeEnvironment J E B D =
      (retainEnvironment J (fst E S) body ≫ routeEnvironment J E B A) ≫
        coprod.map (𝟙 _) (J.map (E ◁ h)) := by
  rw [retainEnvironment_comp]
  have ret : retainLeft J (R := E) (J.map (coprod.map (𝟙 B) h)) =
      J.map (E ◁ coprod.map (𝟙 B) h) := by
    simp only [retainLeft, PremonoidalCategory.leftTensor, PremonoidalCategory.id_whiskerRight,
      Category.id_comp, Functor.StrongPremonoidal.tensor_naturality_right]
    simp
  rw [Category.assoc, ret, route_state, Category.assoc]

private theorem loop_as_iterate {E A B : V} (f : J.obj (E ⊗ A) ⟶ J.obj (B ⨿ A)) :
    contextualLoop J f = iterate (contextualStep J f) ≫ J.map (snd E B) := by
  simp only [contextualLoop, contextualStep, retainEnvironment, routeEnvironment, Category.assoc]

theorem loop_factor (roll : IterationRolling C) {E A B D : V} (h : A ⟶ D)
    (middle : J.obj (E ⊗ D) ⟶ J.obj (B ⨿ A)) :
    contextualLoop J (J.map (E ◁ h) ≫ middle) =
      J.map (E ◁ h) ≫ contextualLoop J (middle ≫ J.map (coprod.map (𝟙 B) h)) := by
  rw [loop_as_iterate J, loop_as_iterate J, contextualStep, contextualStep,
    step_pre J, Category.assoc, step_post J, roll, Category.assoc]

private theorem loop_square {E A B D : V} (h : A ⟶ D)
    (small : J.obj (E ⊗ A) ⟶ J.obj (B ⨿ A))
    (large : J.obj (E ⊗ D) ⟶ J.obj (B ⨿ D))
    (comm : small ≫ J.map (coprod.map (𝟙 B) h) = J.map (E ◁ h) ≫ large) :
    contextualLoop J small = J.map (E ◁ h) ≫ contextualLoop J large := by
  have step : contextualStep J small ≫ coprod.map (𝟙 _) (J.map (E ◁ h)) =
      J.map (E ◁ h) ≫ contextualStep J large := by
    rw [contextualStep, contextualStep, ← step_post J h small, comm, step_pre J, Category.assoc]
  rw [loop_as_iterate J, loop_as_iterate J,
    ElgotFreydCategory.pure_uniformity J _ _ (E ◁ h) step, Category.assoc]

theorem dispatch_square {E A B D : V} (h : A ⟶ D)
    (entry : J.obj E ⟶ J.obj (B ⨿ A))
    (small : J.obj (E ⊗ A) ⟶ J.obj (B ⨿ A))
    (large : J.obj (E ⊗ D) ⟶ J.obj (B ⨿ D))
    (comm : small ≫ J.map (coprod.map (𝟙 B) h) = J.map (E ◁ h) ≫ large) :
    caseWithContext J entry (J.map (snd E B)) (contextualLoop J small) =
      caseWithContext J (entry ≫ J.map (coprod.map (𝟙 B) h)) (J.map (snd E B))
        (contextualLoop J large) := by
  rw [case_state J, loop_square J h small large comm]

theorem dispatch_factor (roll : IterationRolling C) {E A B D : V} (h : A ⟶ D)
    (entry : J.obj E ⟶ J.obj (B ⨿ A)) (middle : J.obj (E ⊗ D) ⟶ J.obj (B ⨿ A)) :
    caseWithContext J entry (J.map (snd E B)) (contextualLoop J (J.map (E ◁ h) ≫ middle)) =
      caseWithContext J (entry ≫ J.map (coprod.map (𝟙 B) h)) (J.map (snd E B))
        (contextualLoop J (middle ≫ J.map (coprod.map (𝟙 B) h))) := by
  rw [case_state J, loop_factor J roll]

end Iteration

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.LiveCoherence
