module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedCallReturns.ConstructorJoin.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.Joined.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithComputedCallReturns.ConstructorJoin

/-! # Soundness of the computed-call constructor join -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedCallReturns.ConstructorJoin

open CategoryTheory CategoryTheory.Limits
open Semantics.Categorical
open LetIter.Semantics.Categorical (TypeModel InstructionModel)
open scoped MonoidalCategory

universe u v w u₁ u₂ v₁ v₂

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] {pe : ε} {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}

theorem ofConstructor (h : WithConstructorSequencing.Joined.Eqv pe Γ r s L) : Eqv pe Γ r s L :=
  WithProjectionReturnsAndUnitEta.WithBranchBinding.mapSeed Or.inl h

theorem ofCall (h : WithComputedCallReturns.Step Γ r s L) : Eqv pe Γ r s L :=
  .extra h.valueBranches.1.hasType h.valueBranches.2.hasType (.inr h)

theorem sound {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
    [CartesianMonoidalCategory V] [SymmetricCategory V]
    [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
    [HasFiniteCoproducts V] [HasFiniteCoproducts C]
    [DistributiveTensor V] [DistributivePremonoidalCategory C]
    [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
    [FreydCategory.CentralUnit J] (M : TypeModel τ V) [InstructionModel J M Φ]
    [RegionTypingCoherent (Φ := Φ) J M]
    (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
      Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)
    (h : Eqv pe Γ r s L) (hr : HasType Γ r L) (hs : HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs :=
  sound_proof J M shared h hr hs

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedCallReturns.ConstructorJoin
