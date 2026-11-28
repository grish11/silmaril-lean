module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProductDestructureReturns.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedCallReturns.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProductDestructureReturns

/-! # Product destructuring in the recursive return fragment -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProductDestructureReturns

open Silmaril Silmaril.Isotope.LambdaSSA
open CfgEta.TypeCategory (returnRegion_typed)
open Paper.Extension.Singleton (ofRegion SeedDenotes)
open Paper.Extension.Singleton.Generation (Generated)
open Paper.WithPairReturns (ProductReturnAgreement ReturnFragmentWithRules)
open Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (duplicate)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

universe u v w m n x y

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "Join" => JoinedStep (τ := τ) (Φ := Φ) pe

/-- The exact product-variable return equation in the opt-in quotient. -/
theorem productReturnAgreement : ProductReturnAgreement Join :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProductDestructureReturns.productReturnAgreement pe

/-- The same induction generates a returned product destructure whose opened
body comes from a recursively generated packed term. -/
theorem generated_returnFragment {X D : τ} {t : Tm Φ} {ht : Tm.HasType [X] t D}
    (h : ReturnFragmentWithRules pe true true ht) : Generated Join (ofRegion Join (returnRegion_typed ht)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProductDestructureReturns.generated_returnFragment pe h

variable {V : Type m} {C : Type n} [Category.{x} V] [Category.{y} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

/-- The single new step is sound when the transported diagonals are central. -/
theorem step_denotes
    (copyCentral : ∀ E : V, PremonoidalCategory.IsCentral (J.map (duplicate E) ≫
      (Functor.StrongPremonoidal.tensorIso (J := J) E E).inv)) :
    SeedDenotes (Seed := Step (τ := τ) (Φ := Φ)) J M :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProductDestructureReturns.step_denotes J M copyCentral

/-- Shared tensor comparisons give coherent denotation for the enlarged join. -/
theorem joined_seedDenotes
    (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
      Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h) :
    SeedDenotes (Seed := Join) J M :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProductDestructureReturns.joined_seedDenotes pe J M shared

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProductDestructureReturns
