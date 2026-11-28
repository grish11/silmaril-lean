module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.Denotation.Tripling.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Singleton.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldWithTriplingDenotation

open Silmaril.Isotope.LambdaSSA.Region
open Paper.WithCaseReturns.BinaryFold (JoinedStep)
open Paper.WithCaseReturns.BinaryFold.WithTripling (Step fromBinaryFold projection_comp_fromBinaryFold)
open Silmaril.Isotope.LambdaSSA
open CategoryTheory CategoryTheory.Limits
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
  (ofRegion projection homRel)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "S" => JoinedStep (τ := τ) (Φ := Φ) pe
set_option hygiene false in
local notation "T" => Step (τ := τ) (Φ := Φ) pe

open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
  (SeedDenotes projection_comp_denoteFunctor denoteFunctor_map_ofRegion)

open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open scoped MonoidalCategory

universe u₁ u₂ v₁ v₂
variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J] (M : TypeModel τ V)
  [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]
  (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
    Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)

set_option hygiene false in
local notation "Old" => Paper.WithCaseReturns.BinaryFold.denoteFunctor (Φ := Φ) pe J M shared

open SingletonDispatcher (payload_labelInject)

set_option backward.isDefEq.respectTransparency false in
include shared in
theorem seedDenotes : SeedDenotes (Seed := T) J M := by
  intro Γ r s L seed hr hs
  rcases seed with inherited | added
  · exact Paper.WithCaseReturns.BinaryFold.seedDenotes pe J M shared inherited hr hs
  cases added with
  | @uniform A B g r s hr' hs' left right =>
    have eq : (Old).map (ofRegion S hr') = (Old).map (ofRegion S hs') := by
      rw [left, right, Functor.map_comp, Paper.WithCaseReturns.BinaryFold.denoteFunctor_map_ternary_uniformity]
    change (Paper.Extension.Singleton.denoteFunctor J M shared (Paper.WithCaseReturns.BinaryFold.seedDenotes pe J M shared)).map
      (ofRegion S hr') = (Paper.Extension.Singleton.denoteFunctor J M shared
        (Paper.WithCaseReturns.BinaryFold.seedDenotes pe J M shared)).map (ofRegion S hs') at eq
    rw [denoteFunctor_map_ofRegion, denoteFunctor_map_ofRegion] at eq
    let X := Silmaril.coprod A (Silmaril.coprod A A)
    have source : J.map (λ_ (M.obj X)).hom ≫ J.map (λ_ (M.obj X)).inv = 𝟙 _ := by
      rw [← J.map_comp, Iso.hom_inv_id, J.map_id]
    have payload : J.map (singletonLabelPayload M B) ≫ J.map (labelInject M 0 (L := [B]) rfl) = 𝟙 _ := by
      rw [← J.map_comp, payload_labelInject, J.map_id]
    change denoteSingletonRegion J M hr = denoteSingletonRegion J M hs at eq
    have closed := congrArg (fun f => J.map (λ_ (M.obj X)).hom ≫ f ≫
      J.map (labelInject M 0 (L := [B]) rfl)) eq
    dsimp only [X] at source closed
    simp only [denoteSingletonRegion, Category.assoc, reassoc_of% source, payload, Category.comp_id] at closed
    exact ⟨_, denoteRegion_spec J M hr, closed.symm ▸ denoteRegion_spec J M hs⟩

set_option hygiene false in
local notation "H" => fromBinaryFold (τ := τ) (Φ := Φ) pe
set_option hygiene false in
local notation "New" => Paper.Extension.Singleton.denoteFunctor J M shared (seedDenotes pe J M shared)

theorem fromBinaryFold_comp_denoteFunctor : (H) ⋙ (New) = (Old) := by
  apply CategoryTheory.Quotient.lift_unique'
  change Paper.Extension.Singleton.projection S ⋙ ((H) ⋙ (New)) = Paper.Extension.Singleton.projection S ⋙ (Old)
  rw [← Functor.assoc, projection_comp_fromBinaryFold]
  exact (projection_comp_denoteFunctor J M shared (seedDenotes pe J M shared)).trans
    (projection_comp_denoteFunctor J M shared (Paper.WithCaseReturns.BinaryFold.seedDenotes pe J M shared)).symm

theorem existsUnique_denoteFactor :
    ∃! G : Paper.WithCaseReturns.BinaryFold.WithTripling.TypeCategory (τ := τ) (Φ := Φ) pe ⥤ C, (H) ⋙ G = (Old) := by
  refine ⟨(New), fromBinaryFold_comp_denoteFunctor pe J M shared, ?_⟩
  intro G factor
  apply CategoryTheory.Quotient.lift_unique'
  change Paper.Extension.Singleton.projection T ⋙ G = Paper.Extension.Singleton.projection T ⋙ (New)
  rw [← projection_comp_fromBinaryFold, Functor.assoc, Functor.assoc,
    factor, fromBinaryFold_comp_denoteFunctor]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldWithTriplingDenotation
