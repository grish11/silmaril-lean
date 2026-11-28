module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProductDestructureReturns.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.BinaryLet.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Singleton.Thms

/-! # Soundness of the opt-in guarded singleton product producer -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ComputedProductProducers

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithComputedProductProducers (Step)
open Paper.Extension.Singleton (SeedDenotes)
open Paper.SingletonReification.BinaryLet (returnPair_denotation)
open Semantics.Categorical
open SingletonDispatcher (payload_labelInject)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

universe u v m n x y

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type m} {C : Type n} [Category.{x} V] [Category.{y} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

set_option backward.isDefEq.respectTransparency false in
theorem step_denotes : SeedDenotes (Seed := Step (τ := τ) (Φ := Φ)) J M := by
  intro Γ r s L step hr hs
  cases step with
  | @producer X A B a ha =>
    let D := product A B
    have equal := returnPair_denotation J M ha
    change denoteSingletonRegion J M hr = denoteSingletonRegion J M hs at equal
    have payload : J.map (singletonLabelPayload M D) ≫ J.map (labelInject M 0 (L := [D]) rfl) = 𝟙 _ := by
      rw [← J.map_comp, payload_labelInject, J.map_id]
    dsimp only [D] at payload
    have source : J.map (λ_ (M.obj X)).hom ≫ J.map (λ_ (M.obj X)).inv = 𝟙 _ := by
      rw [← J.map_comp, Iso.hom_inv_id, J.map_id]
    have eq := congrArg (fun f => J.map (λ_ (M.obj X)).hom ≫ f ≫
      J.map (labelInject M 0 (L := [D]) rfl)) equal
    simp only [denoteSingletonRegion, Category.assoc, reassoc_of% source, payload, Category.comp_id] at eq
    exact ⟨_, denoteRegion_spec J M hr, eq.symm ▸ denoteRegion_spec J M hs⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ComputedProductProducers
