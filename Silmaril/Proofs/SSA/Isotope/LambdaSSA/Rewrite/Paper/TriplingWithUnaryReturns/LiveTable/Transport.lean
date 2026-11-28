module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.Live.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Singleton.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.LiveTable

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open CartesianMonoidalCategory (fst snd)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical (IterationRolling)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical.SingletonDispatcher (route_inl route_inr)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (extend caseWithContext contextualLoop splitMapCoprod)
open Silmaril.Isotope.LetIter.Semantics.Categorical (contextualStep routeEnvironment retainEnvironment)

set_option backward.isDefEq.respectTransparency false

universe u v
section Iteration

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C] [Iteration C]

theorem iterate_iso_of_rolling (roll : IterationRolling C) {A P B : C} (p : A ≅ P)
    (f : A ⟶ B ⨿ A) (g : P ⟶ B ⨿ P)
    (square : f ≫ coprod.map (𝟙 B) p.hom = p.hom ≫ g) :
    iterate f = p.hom ≫ iterate g := by
  let k := g ≫ coprod.map (𝟙 B) p.inv
  have left : p.hom ≫ k = f := by
    dsimp only [k]
    rw [← Category.assoc, ← square, Category.assoc, coprod.map_map,
      Category.comp_id, p.hom_inv_id, coprod.map_id_id, Category.comp_id]
  have right : k ≫ coprod.map (𝟙 B) p.hom = g := by
    dsimp only [k]
    rw [Category.assoc, coprod.map_map, Category.comp_id, p.inv_hom_id,
      coprod.map_id_id, Category.comp_id]
  rw [← left, roll p.hom k, right]

end Iteration

universe u₁ u₂ v₁ v₂
variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]

/-- Route the unchanged environment to the packed state only on recurrence. -/
noncomputable def carryRoute {E A B P : V} (p : E ⊗ A ⟶ P) : E ⊗ (B ⨿ A) ⟶ B ⨿ P :=
  (DistributiveTensor.leftIso E B A).inv ≫ coprod.desc (snd E B ≫ coprod.inl) (p ≫ coprod.inr)

omit [SymmetricCategory V] in
@[reassoc] theorem carryRoute_inl {E A B P : V} (p : E ⊗ A ⟶ P) :
    (E ◁ (coprod.inl : B ⟶ B ⨿ A)) ≫ carryRoute p = snd E B ≫ coprod.inl := by
  change (E ◁ coprod.inl) ≫ (DistributiveTensor.leftIso E B A).inv ≫ _ = _
  rw [← DistributiveTensor.inl_leftHom E B A, Category.assoc]
  change coprod.inl ≫ (DistributiveTensor.leftIso E B A).hom ≫
    (DistributiveTensor.leftIso E B A).inv ≫ _ = _
  simp

omit [SymmetricCategory V] in
@[reassoc] theorem carryRoute_inr {E A B P : V} (p : E ⊗ A ⟶ P) :
    (E ◁ (coprod.inr : A ⟶ B ⨿ A)) ≫ carryRoute p = p ≫ coprod.inr := by
  change (E ◁ coprod.inr) ≫ (DistributiveTensor.leftIso E B A).inv ≫ _ = _
  rw [← DistributiveTensor.inr_leftHom E B A, Category.assoc]
  change coprod.inr ≫ (DistributiveTensor.leftIso E B A).hom ≫
    (DistributiveTensor.leftIso E B A).inv ≫ _ = _
  simp

omit [SymmetricCategory V] in
theorem carryRoute_pre {E F A B P : V} (k : F ⟶ E) (p : E ⊗ A ⟶ P) :
    (k ▷ (B ⨿ A)) ≫ carryRoute p = carryRoute ((k ▷ A) ≫ p) := by
  apply (cancel_epi (DistributiveTensor.leftIso F B A).hom).mp
  apply coprod.hom_ext
  · change coprod.inl ≫ DistributiveTensor.leftHom F B A ≫ _ =
      coprod.inl ≫ DistributiveTensor.leftHom F B A ≫ _
    simp only [DistributiveTensor.inl_leftHom_assoc]
    rw [← Category.assoc _ (k ▷ (B ⨿ A)), MonoidalCategory.whisker_exchange,
      Category.assoc, carryRoute_inl, carryRoute_inl]
    simp
  · change coprod.inr ≫ DistributiveTensor.leftHom F B A ≫ _ =
      coprod.inr ≫ DistributiveTensor.leftHom F B A ≫ _
    simp only [DistributiveTensor.inr_leftHom_assoc]
    rw [← Category.assoc _ (k ▷ (B ⨿ A)), MonoidalCategory.whisker_exchange,
      Category.assoc, carryRoute_inr, carryRoute_inr, Category.assoc]

@[reassoc] theorem carryRoute_image {E A B P : V} (p : E ⊗ A ⟶ P) :
    J.map (carryRoute (B := B) p) ≫ splitMapCoprod J B P =
      routeEnvironment J E B A ≫ coprod.map (J.map (snd E B)) (J.map p) := by
  let route := routeEnvironment J E B A
  have : IsIso route := by
    dsimp only [route, routeEnvironment, splitMapCoprod]
    infer_instance
  apply (cancel_epi (inv route)).mp
  rw [show inv route ≫ routeEnvironment J E B A ≫ coprod.map (J.map (snd E B)) (J.map p) =
    coprod.map (J.map (snd E B)) (J.map p) from IsIso.inv_hom_id_assoc route _]
  apply coprod.hom_ext
  · have left : coprod.inl ≫ inv route = J.map (E ◁ (coprod.inl : B ⟶ B ⨿ A)) := by
      rw [← route_inl J, Category.assoc]
      rw [show routeEnvironment J E B A ≫ inv route = 𝟙 _ from IsIso.hom_inv_id route, Category.comp_id]
    rw [← Category.assoc, left, ← J.map_comp_assoc, carryRoute_inl, J.map_comp,
      Category.assoc, splitMapCoprod, map_inl_inv_coprodComparison, coprod.inl_map]
  · have right : coprod.inr ≫ inv route = J.map (E ◁ (coprod.inr : A ⟶ B ⨿ A)) := by
      rw [← route_inr J, Category.assoc]
      rw [show routeEnvironment J E B A ≫ inv route = 𝟙 _ from IsIso.hom_inv_id route, Category.comp_id]
    rw [← Category.assoc, right, ← J.map_comp_assoc, carryRoute_inr, J.map_comp,
      Category.assoc, splitMapCoprod, map_inr_inv_coprodComparison, coprod.inr_map]

theorem packed_dispatch_of_iterate {E A B P : V} (p : E ⊗ A ≅ P)
    (entry : J.obj E ⟶ J.obj (B ⨿ A)) (body : J.obj (E ⊗ A) ⟶ J.obj (B ⨿ A))
    (g : J.obj P ⟶ J.obj B ⨿ J.obj P)
    (square : retainEnvironment J (fst E A) body ≫ J.map (carryRoute p.hom) ≫
      splitMapCoprod J B P = J.map p.hom ≫ g)
    (transport : ∀ {f : J.obj (E ⊗ A) ⟶ J.obj B ⨿ J.obj (E ⊗ A)},
      f ≫ coprod.map (𝟙 _) (J.map p.hom) = J.map p.hom ≫ g →
      iterate f = J.map p.hom ≫ iterate g) :
    caseWithContext J entry (J.map (snd E B)) (contextualLoop J body) =
      extend J entry ≫ J.map (carryRoute p.hom) ≫ splitMapCoprod J B P ≫
        coprod.desc (𝟙 _) (iterate g) := by
  have stepSquare :
      (contextualStep J body ≫ coprod.map (J.map (snd E B)) (𝟙 _)) ≫
        coprod.map (𝟙 _) (J.map p.hom) = J.map p.hom ≫ g := by
    rw [Category.assoc, coprod.map_map, Category.comp_id, Category.id_comp]
    simpa only [contextualStep, Category.assoc, ← carryRoute_image J p.hom] using square
  have loop : contextualLoop J body = J.map p.hom ≫ iterate g := by
    have shape : contextualLoop J body = iterate (contextualStep J body) ≫ J.map (snd E B) := by
      simp only [contextualLoop, contextualStep, retainEnvironment, routeEnvironment, Category.assoc]
    exact shape.trans ((ElgotCategory.naturality (contextualStep J body) (J.map (snd E B))).trans
      (transport stepSquare))
  rw [loop, carryRoute_image_assoc]
  simp only [caseWithContext, Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind,
    routeEnvironment, Category.assoc, coprod.map_desc, Category.comp_id]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.LiveTable
