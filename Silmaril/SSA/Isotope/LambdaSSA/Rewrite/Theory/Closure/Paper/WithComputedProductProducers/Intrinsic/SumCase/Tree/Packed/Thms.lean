module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Tree.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.ExitPacking.Denotation.Thms

/-! # The selected case tree fold in the packed singleton interface -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic

open Silmaril.Isotope.LambdaSSA
open Paper.WithProjectionReturnsAndUnitEta (denoteArrow denoteArrow_ofRegion)
open Paper.WithProjectionReturnsAndUnitEta.ExitPacking (packArrow)
open Semantics.Categorical
open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open scoped MonoidalCategory

universe u v m n x y

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type m} {C : Type n} [Category.{x} V] [Category.{y} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]
  (shared : ∀ E S : V, ∃ h : J.obj E ⊗ J.obj S = J.obj (E ⊗ S),
    Functor.StrongPremonoidal.tensorIso (J := J) E S = eqToIso h)
  {X : τ} {L : LCtx τ}

/-- The interpreted joined packed arrow is the selected tree fold with its
outward labels tagged in the public packed sum. -/
theorem CaseTree.denote_packArrow (p : CaseTree Φ X L) :
    denoteArrow J M shared (packArrow p.elaborate.property) =
      p.targetArrow J M ≫ J.map (packLabel M L) := by
  rw [WithProjectionReturnsAndUnitEta.ExitPacking.denote_packArrow J M shared, ← (p.targetDenotes J M shared).eq_denote J M]
  simp only [ctxObj, Category.assoc, ← J.map_comp_assoc, Iso.inv_hom_id, J.map_id, Category.id_comp]

include shared in
/-- The same equation directly at the actual native packed representative. -/
theorem CaseTree.denote_packedElaboration (p : CaseTree Φ X L) :
    denoteSingletonRegion J M p.elaborate.property.packExits.hasType =
      p.targetArrow J M ≫ J.map (packLabel M L) :=
  (denoteArrow_ofRegion J M shared p.elaborate.property.packExits).symm.trans
    (p.denote_packArrow J M shared)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic
