module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.Reflection.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.Unrolling.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Denotation.Preservation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Rounds.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Singleton.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonRounds

/-! # Unrolled written loops are valid in every supported model -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithAdministrativeReturns
open Paper.WithAdministrativeReturns.WithGuardedTablePacking (Valid)
open Paper.Extension.Singleton (ofRegion ofType sumCofan sumCofanIsColimit iterateSum)
open Paper.Extension.Singleton.Rounds
open Paper.Extension.Singleton.ValueCoproducts (exactCopair)
open Paper.Extension.Singleton.Generation
open Semantics.Categorical
open Semantics.Categorical.SingletonDispatcher (payload_labelInject)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

universe u v w u₁ u₂ v₁ v₂
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]
  (shared : ∀ E X : V, ∃ h : J.obj E ⊗ J.obj X = J.obj (E ⊗ X),
    Functor.StrongPremonoidal.tensorIso (J := J) E X = eqToIso h)
  {A B : τ}

set_option hygiene false in
local notation "N" => WithGuardedTablePacking.Step (τ := τ) (Φ := Φ) pe
set_option hygiene false in
local notation "G" => WithGuardedTablePacking.denoteFunctor (Φ := Φ) pe J M shared
set_option hygiene false in
local notation "T" => Coordinates.ofModel (τ := τ) J M

set_option backward.isDefEq.respectTransparency false

/-- A step of the quotient in the model, at the chosen coproduct. -/
noncomputable abbrev stepC (s : ofType N A ⟶ ofType N (Silmaril.coprod B A)) :
    J.obj (M.obj A) ⟶ J.obj (M.obj B) ⨿ J.obj (M.obj A) :=
  (G).map s ≫ ((T).sumIso B A).hom

include shared in
theorem pres_inl : (G).map (sumCofan N B A).inl = coprod.inl ≫ ((T).sumIso B A).inv := by
  have p := (Paper.Extension.Singleton.denoteFunctor_preserves J M shared
    (WithGuardedTablePacking.seedDenotes (Φ := Φ) pe J M shared)).inl B A
  simp only [mapInCoordinates, Iso.refl_inv, Iso.refl_hom, Category.id_comp] at p
  exact (Category.comp_id _).symm.trans p

include shared in
theorem pres_inr : (G).map (sumCofan N B A).inr = coprod.inr ≫ ((T).sumIso B A).inv := by
  have p := (Paper.Extension.Singleton.denoteFunctor_preserves J M shared
    (WithGuardedTablePacking.seedDenotes (Φ := Φ) pe J M shared)).inr B A
  simp only [mapInCoordinates, Iso.refl_inv, Iso.refl_hom, Category.id_comp] at p
  exact (Category.comp_id _).symm.trans p

theorem step_then (s t : ofType N A ⟶ ofType N (Silmaril.coprod B A)) :
    stepC pe J M shared (thenExact N s t) =
      stepC pe J M shared s ≫ coprod.desc coprod.inl (stepC pe J M shared t) := by
  let c : J.obj (M.obj (Silmaril.coprod B A)) ⟶ J.obj (M.obj (Silmaril.coprod B A)) :=
    (G).map (exactCopair N (sumCofan N B A).inl t)
  have facl : (sumCofan N B A).inl ≫ exactCopair N (sumCofan N B A).inl t = (sumCofan N B A).inl :=
    (sumCofanIsColimit N B A).fac (BinaryCofan.mk (sumCofan N B A).inl t) ⟨WalkingPair.left⟩
  have facr : (sumCofan N B A).inr ≫ exactCopair N (sumCofan N B A).inl t = t :=
    (sumCofanIsColimit N B A).fac (BinaryCofan.mk (sumCofan N B A).inl t) ⟨WalkingPair.right⟩
  have left : (coprod.inl ≫ ((T).sumIso B A).inv) ≫ c = coprod.inl ≫ ((T).sumIso B A).inv :=
    (congrArg (· ≫ c) (pres_inl pe J M shared).symm).trans
      ((((G).map_comp _ _).symm.trans (congrArg (G).map facl)).trans (pres_inl pe J M shared))
  have right : (coprod.inr ≫ ((T).sumIso B A).inv) ≫ c = (G).map t :=
    (congrArg (· ≫ c) (pres_inr pe J M shared).symm).trans
      (((G).map_comp _ _).symm.trans (congrArg (G).map facr))
  have copair : c ≫ ((T).sumIso B A).hom =
      ((T).sumIso B A).hom ≫ coprod.desc coprod.inl (stepC pe J M shared t) := by
    rw [← Iso.inv_comp_eq]
    apply coprod.hom_ext
    · rw [← Category.assoc, ← Category.assoc, left, Category.assoc, Iso.inv_hom_id, Category.comp_id,
        coprod.inl_desc]
    · rw [← Category.assoc, ← Category.assoc, right, coprod.inr_desc]
  have comp : (G).map (thenExact N s t) = (G).map s ≫ c := (G).map_comp _ _
  change (G).map (thenExact N s t) ≫ ((T).sumIso B A).hom = _
  rw [comp, Category.assoc, copair, ← Category.assoc]

theorem step_rounds (s : ofType N A ⟶ ofType N (Silmaril.coprod B A)) :
    ∀ n, stepC pe J M shared (rounds N s n) = roundsStep (stepC pe J M shared s) n
  | 0 => rfl
  | n + 1 => (step_then pe J M shared s (rounds N s n)).trans
      (congrArg (fun k => stepC pe J M shared s ≫ coprod.desc coprod.inl k) (step_rounds s n))

/-- The model's arrows of the two loops agree, for every round count. -/
theorem map_iterate_rounds (s : ofType N A ⟶ ofType N (Silmaril.coprod B A)) (n : Nat) :
    (G).map (iterateSum N (rounds N s n)) = (G).map (iterateSum N s) := by
  have loop (r : ofType N A ⟶ ofType N (Silmaril.coprod B A)) :
      (G).map (iterateSum N r) = CategoryTheory.iterate (stepC pe J M shared r) :=
    Paper.Extension.Singleton.denoteFunctor_map_iterateSum J M shared
      (WithGuardedTablePacking.seedDenotes pe J M shared) r
  rw [loop, loop, step_rounds, iterate_roundsStep]

include pe shared in
theorem singleton_rounds {s : Region Φ} (hs : ValueBranches [A] s [Silmaril.coprod B A]) (n : Nat) :
    denoteSingletonRegion J M
      (SyntacticCategory.iterateRegion_valueBranches (roundsRegion_typed hs n)).hasType =
    denoteSingletonRegion J M (SyntacticCategory.iterateRegion_valueBranches hs).hasType := by
  have literal {r : Region Φ} (hr : ValueBranches [A] r [Silmaril.coprod B A]) :
      (G).map (iterateSum N (ofRegion N hr)) =
        denoteSingletonRegion J M (SyntacticCategory.iterateRegion_valueBranches hr).hasType :=
    (congrArg (G).map (SingletonRounds.ofRegion_iterateRegion N hr)).symm.trans
      (Paper.Extension.Singleton.denoteFunctor_map_ofRegion J M shared
        (WithGuardedTablePacking.seedDenotes pe J M shared) _)
  rw [← literal (roundsRegion_typed hs n), ← literal hs, ofRegion_roundsRegion]
  exact map_iterate_rounds pe J M shared (ofRegion N hs) n

include pe shared in
theorem denote_rounds {s : Region Φ} (hs : ValueBranches [A] s [Silmaril.coprod B A]) (n : Nat) :
    denoteRegion J M (SyntacticCategory.iterateRegion_valueBranches (roundsRegion_typed hs n)).hasType =
      denoteRegion J M (SyntacticCategory.iterateRegion_valueBranches hs).hasType := by
  have eq := singleton_rounds pe J M shared hs n
  have source : J.map (λ_ (M.obj A)).hom ≫ J.map (λ_ (M.obj A)).inv = 𝟙 _ := by
    rw [← J.map_comp, Iso.hom_inv_id, J.map_id]
  have payload : J.map (singletonLabelPayload M B) ≫ J.map (labelInject M 0 (L := [B]) rfl) = 𝟙 _ := by
    rw [← J.map_comp, payload_labelInject, J.map_id]
  have closed := congrArg (fun f => J.map (λ_ (M.obj A)).hom ≫ f ≫
    J.map (labelInject M 0 (L := [B]) rfl)) eq
  simp only [denoteSingletonRegion, Category.assoc, reassoc_of% source, payload, Category.comp_id] at closed
  exact closed

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking
