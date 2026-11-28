module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Tree.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedCaseTree

/-! # Exact denotation of recursively selected native cases -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic

open Silmaril Silmaril.Isotope.LambdaSSA
open Semantics.Categorical
open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open scoped MonoidalCategory

universe u v m n x y

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {X : τ} {L : LCtx τ}

/-- The shallow presentation and its two-leaf tree elaborate to the same region. -/
theorem SumCase.toTree_elaborate (p : SumCase Φ X L) :
    p.toTree.elaborate.val = p.elaborate.val := by
  simp only [SumCase.toTree, SumCase.elaborate, CaseTree.elaborate, CaseArm.elaborate,
    PackedBody.applyPacked, substVars_renameLabels]

variable {V : Type m} {C : Type n} [Category.{x} V] [Category.{y} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C)
  (M : TypeModel τ V) [InstructionModel J M Φ]

theorem SumCase.toTree_targetArrow [DistributiveFreydCategory J] (p : SumCase Φ X L) :
    p.toTree.targetArrow J M = p.targetArrow J M :=
  rfl

variable [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (shared : ∀ E S : V, ∃ h : J.obj E ⊗ J.obj S = J.obj (E ⊗ S),
    Functor.StrongPremonoidal.tensorIso (J := J) E S = eqToIso h)

include shared in
/-- The recursive categorical fold is a structural witness for the exact
native elaboration, at its original ordered outward interface. -/
theorem CaseTree.targetDenotes (p : CaseTree Φ X L) :
    RegionDenotes J M p.elaborate.property.hasType (J.map (λ_ (M.obj X)).hom ≫ p.targetArrow J M) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedCaseTree.tree_denotes J M shared p

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic
