module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.Denotation.Defs

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns

open Silmaril.Isotope.LambdaSSA.Region
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls (Step)
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns
  (fromWithComputedCalls projection_comp_fromWithComputedCalls denoteFunctor seedDenotes)
open Paper.Extension.Singleton (projection projection_comp_denoteFunctor)

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

universe u v w m n x y
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)
  {V : Type m} {C : Type n} [Category.{x} V] [Category.{y} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]
  (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
    Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)

theorem fromWithComputedCalls_comp_denoteFunctor :
    fromWithComputedCalls (τ := τ) (Φ := Φ) pe ⋙ denoteFunctor pe J M shared =
      Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.denoteFunctor pe J M shared := by
  apply CategoryTheory.Quotient.lift_unique'
  change projection (Step pe) ⋙ (fromWithComputedCalls pe ⋙ denoteFunctor pe J M shared) =
    projection (Step pe) ⋙ Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.denoteFunctor pe J M shared
  rw [← Functor.assoc, projection_comp_fromWithComputedCalls]
  exact (projection_comp_denoteFunctor J M shared (seedDenotes pe J M shared)).trans
    (projection_comp_denoteFunctor J M shared
      (Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.seedDenotes pe J M shared)).symm

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns
