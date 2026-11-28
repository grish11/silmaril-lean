module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.Denotation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingUnaryProducer.Denotation

/-! # Denotation of unary producers before and after return lowering -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.UnaryProducer

open Silmaril.Isotope.LambdaSSA
open CategoryTheory CategoryTheory.Limits
open Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CfgEta.TypeCategory (returnRegion returnRegion_typed)
open Paper.RetainedLet (returnOnce)
open Paper.UnaryReturn (returnOnce_valueBranches)
open scoped MonoidalCategory

universe u v m n x y
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type m} {C : Type n} [Category.{x} V] [Category.{y} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]
  (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
    Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)

include shared in
/-- The typed unary producer can be lowered or bound once before the same
continuation. The continuation receives the result in front of the original
capture list, at its original ordered exits. -/
theorem lowering_post_denotation {Γ : VCtx τ} {A D : τ} {a b : Tm Φ}
    (ha : Tm.HasType Γ a A) (hb : Tm.HasType (A :: Γ) b D)
    {L : LCtx τ} {σ : Nat → Region Φ} (hσ : LSubst.ValueFamily Γ [D] L σ) :
    let ht := Tm.HasType.let₁ ha hb
    denoteRegion J M ((returnRegion_typed ht).lsubst hσ).hasType =
      denoteRegion J M ((returnOnce_valueBranches ht).lsubst hσ).hasType :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingUnaryProducer.lowering_post_denotation
    J M shared ha hb hσ

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.UnaryProducer
