module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Generation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Denotation.UniversalProperty.Thms
import Mathlib.CategoryTheory.Whiskering

/-! # Model interpretation on the raw generated domain -/

public section

universe u v w u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Generation

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Paper.Extension.Singleton.Generation (Coordinates)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)
  {V : Type u₁} {C : Type u₂} [CategoryTheory.Category.{v₁} V] [CategoryTheory.Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]
  (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
    Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)

local notation "Join" => WithPairReturns.JoinedStep (τ := τ) (Φ := Φ) pe
local notation "RawDomain" => Category (τ := τ) (Φ := Φ) pe
local notation "GuardedInterpretation" => Paper.Extension.Singleton.Generation.Domain.Interpretation
  Join (Coordinates.ofModel J M) (InstructionModel.denote (J := J) (M := M))

/-- Interpret the raw generated domain in the same coherent model as the
guarded generated domain, using normalization before interpretation. -/
@[expose] noncomputable def generatedInterpretation : RawDomain ⥤ C :=
  normalizeGenerated pe ⋙ (WithPairReturns.generatedInterpretation (Φ := Φ) pe J M shared).functor

/-- A preserving guarded interpretation agrees with the canonical raw one
at the model coordinates after precomposing with normalization. -/
theorem generatedInterpretation_map_eq (K : GuardedInterpretation) {A B : τ}
    (f : ofType (Φ := Φ) pe A ⟶ ofType pe B) :
    (generatedInterpretation pe J M shared).map f =
      Paper.Extension.Singleton.Generation.Domain.mapInCoordinates Join K.functor K.objIso
        ((normalizeGenerated pe).map f) :=
  WithPairReturns.generatedInterpretation_map_eq pe J M shared K ((normalizeGenerated pe).map f)

/-- The prescribed type components determine a unique natural comparison on
the raw generated domain with each precomposed guarded interpretation. -/
theorem generatedInterpretation_universal (K : GuardedInterpretation) :
    ∃! e : generatedInterpretation pe J M shared ≅ normalizeGenerated pe ⋙ K.functor,
      ∀ A : τ, e.hom.app (ofType pe A) = (K.objIso A).inv := by
  obtain ⟨e, he, _⟩ := WithPairReturns.generatedInterpretation_universal pe J M shared K
  refine ⟨Functor.isoWhiskerLeft (normalizeGenerated pe) e, he, fun _ h => Iso.ext ?_⟩
  ext X
  exact (h X.obj.as).trans (he X.obj.as).symm

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Generation
