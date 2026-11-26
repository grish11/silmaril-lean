module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProductDestructureReturns.Generation.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ComputedProductProducers

/-! # Soundness and generation with opt-in computed product producers -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers

open Silmaril Silmaril.Isotope.LambdaSSA
open Paper.Extension.Singleton (ofRegion SeedDenotes)
open Paper.Extension.Singleton.Generation (Generated)
open Paper.WithProductDestructureReturns
  (ProductProducerAgreement GuardedFragmentWithProducts generated_guardedFragment_with_products)
open Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

universe u v w m n x y

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "Join" => JoinedStep (τ := τ) (Φ := Φ) pe

/-- The joined seed supplies the exact producer equation. -/
theorem productProducerAgreement : ProductProducerAgreement Join := fun ha =>
  let step := Step.producer ha
  .extra step.valueBranches.1.hasType step.valueBranches.2.hasType (.inr step)

/-- The same structural induction now accepts computed product scrutinees. -/
theorem generated_guardedFragment {X D : τ} {r : Region Φ} {hr : ValueBranches [X] r [D]}
    (h : GuardedFragmentWithProducts pe true hr) : Generated Join (ofRegion Join hr) :=
  generated_guardedFragment_with_products pe Join Or.inl (computedProducts := true) (fun _ => productProducerAgreement pe) h

variable {V : Type m} {C : Type n} [Category.{x} V] [Category.{y} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

/-- The producer step is sound by the existing guarded singleton denotation
equation, transported back to the exact input and exit interfaces. -/
theorem step_denotes : SeedDenotes (Seed := Step (τ := τ) (Φ := Φ)) J M :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ComputedProductProducers.step_denotes J M

/-- The extra step preserves soundness under the same shared tensor assumptions as the previous join. -/
theorem joined_seedDenotes
    (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
      Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h) :
    SeedDenotes (Seed := Join) J M := fun step hr hs =>
  step.elim (fun old => WithProductDestructureReturns.joined_seedDenotes pe J M shared old hr hs)
    (fun new => step_denotes J M new hr hs)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers
