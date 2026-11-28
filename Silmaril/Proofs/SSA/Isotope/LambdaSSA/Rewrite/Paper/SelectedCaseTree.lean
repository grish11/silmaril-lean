module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Tree.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.Selected.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.LabelRenaming.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Naturality.Thms

/-! # Structural denotation of the selected case tree -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedCaseTree

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithComputedProductProducers.Intrinsic
open Semantics.Categorical
open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel case_pre_map)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (extend duplicate)
open scoped MonoidalCategory

universe u v m n x y

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type m} {C : Type n} [Category.{x} V] [Category.{y} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ]
  (shared : ∀ E S : V, ∃ h : J.obj E ⊗ J.obj S = J.obj (E ⊗ S),
    Functor.StrongPremonoidal.tensorIso (J := J) E S = eqToIso h)
  {X : τ} {L : LCtx τ}

private theorem bind_projection {E A D : V} (f : J.obj E ⟶ J.obj A) (k : A ⟶ D) :
    Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind J f
      (J.map (CartesianMonoidalCategory.snd E A ≫ k)) = f ≫ J.map k := by
  have project : extend J f ≫ J.map (CartesianMonoidalCategory.snd E A) = f := by
    simp only [extend, PremonoidalCategory.leftTensor, PremonoidalCategory.id_whiskerRight,
      Category.id_comp, Category.assoc]
    rw [FreydCategory.whiskerLeft_snd J E f, ← J.map_comp_assoc]
    simp [duplicate]
  rw [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, J.map_comp, ← Category.assoc, project]

include shared in
set_option backward.isDefEq.respectTransparency false in
theorem tree_denotes (p : CaseTree Φ X L) :
    RegionDenotes J M p.elaborate.property.hasType (J.map (λ_ (M.obj X)).hom ≫ p.targetArrow J M) := by
  induction p with
  | exit slot hi body =>
    have d := (body.targetDenotes J M shared).renameLabels J M (singletonExitRen hi)
    simpa only [CaseTree.elaborate, CaseTree.targetArrow, Category.assoc,
      ← J.map_comp, labelInject_labelMap] using d
  | @taggedExit X P D L slot hi tag body =>
    have dt := body.targetDenotes J M
    cases tag with
    | inl A B =>
      have branch := RegionDenotes.br (h := hi)
        (Denotes.inl (B := B) (Denotes.var (J := J) (M := M) (Φ := Φ) (i := 0) (rfl : At [P, X] 0 P)))
      simpa only [CaseTree.elaborate, CaseTree.targetArrow, ExitTag.valueMap, lookup, ctxObj,
        Category.assoc, ← J.map_comp, bind_projection J] using RegionDenotes.let₁ dt branch
    | inr A _ =>
      have branch := RegionDenotes.br (h := hi)
        (Denotes.inr (A := A) (Denotes.var (J := J) (M := M) (Φ := Φ) (i := 0) (rfl : At [P, X] 0 P)))
      simpa only [CaseTree.elaborate, CaseTree.targetArrow, ExitTag.valueMap, lookup, ctxObj,
        Category.assoc, ← J.map_comp, bind_projection J] using RegionDenotes.let₁ dt branch
  | case A B a left right il ir =>
    have dl := applyPacked_denotes J M il
      (applyPacked_typed_exits left.elaborate.property).hasType
    have dr := applyPacked_denotes J M ir
      (applyPacked_typed_exits right.elaborate.property).hasType
    have dn := RegionDenotes.case (a.targetDenotes J M) dl dr
    simpa only [CaseTree.elaborate, CaseTree.targetArrow, Category.assoc, case_pre_map] using dn

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedCaseTree
