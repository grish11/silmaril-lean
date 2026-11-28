module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedSumCase

/-! # The selected categorical interpretation of a native sum case -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic

open Silmaril Silmaril.Isotope.LambdaSSA
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
  (M : TypeModel τ V) [InstructionModel J M Φ]
  (shared : ∀ E S : V, ∃ h : J.obj E ⊗ J.obj S = J.obj (E ⊗ S),
    Functor.StrongPremonoidal.tensorIso (J := J) E S = eqToIso h)
  {X A : τ} {L : LCtx τ}

omit [FreydCategory.CentralUnit J] in
/-- Supplying a retained input and payload transports a selected body witness
at any ordered outward interface. -/
theorem applyPacked_denotes {p : Region Φ} {hp : HasType [product X A] p L}
    {g : J.obj (M.obj (product X A)) ⟶ J.obj (labelObj M L)}
    (d : RegionDenotes J M hp (J.map (λ_ (M.obj (product X A))).hom ≫ g))
    (unpacked : HasType [A, X] (Paper.PackedBody.applyPacked p) L) :
    RegionDenotes J M unpacked
      (J.map ((λ_ (M.obj X)).hom ▷ M.obj A) ≫ J.map (M.productIso X A).inv ≫ g) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedSumCase.applyPacked_denotes J M d unpacked

include shared in
/-- The arm's selected witness uses the actual packed substitution and outward
label renaming of the native region. -/
theorem CaseArm.targetDenotes (arm : CaseArm Φ X A L) :
    RegionDenotes J M arm.elaborate.property.hasType
      (J.map ((λ_ (M.obj X)).hom ▷ M.obj A) ≫ arm.targetArrow J M) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedSumCase.arm_denotes J M shared arm

include shared in
/-- The exact native case elaboration has the structural denotation obtained
from the selected discriminator and both continuations, at their ordered exit context. -/
theorem SumCase.targetDenotes (p : SumCase Φ X L) :
    RegionDenotes J M p.elaborate.property.hasType (J.map (λ_ (M.obj X)).hom ≫ p.targetArrow J M) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedSumCase.case_denotes J M shared p

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic
