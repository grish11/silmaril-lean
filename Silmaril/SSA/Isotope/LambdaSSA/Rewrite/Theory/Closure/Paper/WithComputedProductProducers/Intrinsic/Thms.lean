module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Denotation.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.IntrinsicProductReturns

/-! # The intrinsic elaboration agrees with the guarded generators -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic

open Silmaril Silmaril.Isotope.LambdaSSA
open Paper.WithPairReturns (ReturnFragmentWithRules)
open Paper.WithProductDestructureReturns (GuardedFragmentWithProducts)
open Paper.Extension.Singleton (ofRegion denoteFunctor denoteFunctor_map_ofRegion)
open Paper.Extension.Singleton.Generation (Generated)
open CfgEta.TypeCategory (returnRegion_typed)
open Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

universe u v w m n x y

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "Join" => JoinedStep (τ := τ) (Φ := Φ) pe

variable {X D : τ}

/-- The exact elaborated term belongs to the returned-term grammar. -/
theorem Term.returnFragment (t : Term Φ X D) :
    ReturnFragmentWithRules pe true true t.elaborate.property :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.IntrinsicProductReturns.term_fragment pe t

/-- The exact elaborated region belongs to the guarded grammar with computed product producers. -/
theorem Program.guardedFragment (p : Program Φ X D) :
    GuardedFragmentWithProducts pe true p.elaborate.property :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.IntrinsicProductReturns.program_fragment pe p

/-- The returned region and the direct generator interpretation agree in the syntax quotient. -/
theorem Term.arrow_eq_generatorArrow (t : Term Φ X D) :
    ofRegion Join (returnRegion_typed t.elaborate.property) = t.generatorArrow Join :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.IntrinsicProductReturns.term_arrow_eq_generator pe t

/-- This comparison uses only the guarded equations at the selected typing. -/
theorem Program.arrow_eq_generatorArrow (p : Program Φ X D) :
    p.arrow pe = p.generatorArrow Join :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.IntrinsicProductReturns.program_arrow_eq_generator pe p

theorem Program.generated (p : Program Φ X D) : Generated Join (p.arrow pe) :=
  generated_guardedFragment pe (p.guardedFragment pe)

variable {V : Type m} {C : Type n} [Category.{x} V] [Category.{y} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

/-- In the existing coherent shared-tensor model, the denotation of the
selected elaboration is the image of its generator interpretation. -/
theorem Program.denote_eq_map_generatorArrow
    (shared : ∀ A B : V, ∃ h : J.obj A ⊗ J.obj B = J.obj (A ⊗ B),
      Functor.StrongPremonoidal.tensorIso (J := J) A B = eqToIso h) (p : Program Φ X D) :
    denoteSingletonRegion J M p.elaborate.property.hasType =
      (denoteFunctor J M shared (joined_seedDenotes pe J M shared)).map (p.generatorArrow Join) := by
  rw [← p.arrow_eq_generatorArrow pe]
  exact (denoteFunctor_map_ofRegion J M shared (joined_seedDenotes pe J M shared) p.elaborate.property).symm

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic
