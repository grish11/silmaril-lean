module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProductDestructureReturns.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedCallReturns.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedLet.Generation.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Thms

/-! # Sound product-variable return fusion and recursive generation -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProductDestructureReturns

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithProductDestructureReturns
open Paper.WithPairReturns (CallReturnAgreement ProductReturnAgreement ReturnFragmentWithRules generated_returnFragment_with_rules)
open Paper.Extension.Singleton (ofRegion SeedDenotes)
open Paper.Extension.Singleton.Generation (Generated)
open CfgEta.TypeCategory (returnRegion_typed)
open Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel duplicate_central_of_tensor_eqToIso)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (duplicate)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

universe u v w m n x y

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "Join" => JoinedStep (τ := τ) (Φ := Φ) pe

theorem callReturnAgreement : CallReturnAgreement Join := by
  intro Γ a p ha
  let step := Paper.WithComputedCallReturns.Step.seq p ha
  exact .extra step.valueBranches.1.hasType step.valueBranches.2.hasType (.inl (.inr step))

theorem productReturnAgreement : ProductReturnAgreement Join := by
  intro X A D b hb
  let step := Step.unpack hb
  exact .extra step.valueBranches.1.hasType step.valueBranches.2.hasType (.inr step)

theorem generated_returnFragment {X D : τ} {t : Tm Φ} {ht : Tm.HasType [X] t D}
    (h : ReturnFragmentWithRules pe true true ht) : Generated Join (ofRegion Join (returnRegion_typed ht)) :=
  generated_returnFragment_with_rules pe Join (fun step => .inl (.inl step))
    (fun _ => callReturnAgreement pe) (fun _ => productReturnAgreement pe) h

variable {V : Type m} {C : Type n} [Category.{x} V] [Category.{y} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

theorem step_denotes
    (copyCentral : ∀ E : V, PremonoidalCategory.IsCentral (J.map (duplicate E) ≫
      (Functor.StrongPremonoidal.tensorIso (J := J) E E).inv)) :
    SeedDenotes (Seed := Step (τ := τ) (Φ := Φ)) J M := by
  intro Γ r s L h hr hs
  cases h with
  | unpack hb =>
    have eq := Paper.RetainedLet.unpack_return_let₂_denotation J M copyCentral hb
    exact ⟨_, denoteRegion_spec J M hr, eq.symm ▸ denoteRegion_spec J M hs⟩

theorem joined_seedDenotes
    (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
      Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h) :
    SeedDenotes (Seed := Join) J M := by
  intro Γ r s L h hr hs
  rcases h with old | step
  · exact Paper.WithComputedCallReturns.joined_seedDenotes pe J M shared old hr hs
  · apply step_denotes J M _ step hr hs
    intro E
    obtain ⟨e, he⟩ := shared E E
    exact duplicate_central_of_tensor_eqToIso J E e he

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProductDestructureReturns
