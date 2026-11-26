module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Operations.Categorical.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Iteration.Thms

/-! # The exact-type raw and guarded singleton comparison -/

public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Operations

open Silmaril CategoryTheory CategoryTheory.Limits
open Paper.Extension.Singleton (ofType)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

local notation "Join" => WithPairReturns.JoinedStep (τ := τ) (Φ := Φ) pe
local notation "H" => RawHom (Φ := Φ) pe
local notation "G" => ofType (Φ := Φ) Join

/-- An identity-on-types comparison with the operations of the ordered-pair
raw and guarded syntax quotients. The feedback field uses the bind-first
operation at the exact sum type. -/
structure OperationIso where
  homEquiv (A B : τ) : H A B ≃ (G A ⟶ G B)
  map_id (A : τ) : homEquiv A A (identity pe A) = 𝟙 (G A)
  map_comp {A B D : τ} (f : H A B) (g : H B D) :
    homEquiv A D (compose pe f g) = homEquiv A B f ≫ homEquiv B D g
  map_whiskerLeft (X : τ) {A B : τ} (f : H A B) :
    homEquiv (product X A) (product X B) (whiskerLeft pe X f) =
      Extension.Singleton.whiskerLeft Join (G X) (homEquiv A B f)
  map_whiskerRight (X : τ) {A B : τ} (f : H A B) :
    homEquiv (product A X) (product B X) (whiskerRight pe X f) =
      Extension.Singleton.whiskerRight Join (homEquiv A B f) (G X)
  map_exactCopair {A B D : τ} (f : H A D) (g : H B D) :
    homEquiv (coprod A B) D (exactCopair pe f g) =
      Extension.Singleton.ValueCoproducts.exactCopair Join (homEquiv A D f) (homEquiv B D g)
  map_iterateSum {A B : τ} (f : H A (coprod B A)) :
    homEquiv A B (iterateSum pe f) = Extension.Singleton.iterateSum Join (homEquiv A (coprod B A) f)
  map_primitive (p : Φ) :
    homEquiv (instrSrc p) (instrTrg p) (primitive (τ := τ) pe p) =
      Extension.Singleton.Generation.primitive Join p
  map_discard (A : τ) :
    homEquiv A unit (discard pe A) = Extension.Singleton.discardArrow Join A
  map_diagonal (A : τ) :
    homEquiv A (product A A) (diagonal pe A) = Extension.Singleton.diagonalArrow Join (G A)
  map_productFst (A B : τ) :
    homEquiv (product A B) A (productFst pe A B) = Extension.Singleton.productFst Join A B
  map_productSnd (A B : τ) :
    homEquiv (product A B) B (productSnd pe A B) = Extension.Singleton.productSnd Join A B
  map_sumInl (A B : τ) :
    homEquiv A (coprod A B) (sumInl pe A B) = (Extension.Singleton.sumCofan Join A B).inl
  map_sumInr (A B : τ) :
    homEquiv B (coprod A B) (sumInr pe A B) = (Extension.Singleton.sumCofan Join A B).inr
  map_fromEmpty (A : τ) :
    homEquiv empty A (fromEmpty pe A) = (Extension.Singleton.emptyIsInitial Join).to (G A)
  map_braid (A B : τ) :
    homEquiv (product A B) (product B A) (braid pe A B) =
      (Extension.Singleton.braidIso Join (G A) (G B)).hom
  map_associate (A B C : τ) :
    homEquiv (product (product A B) C) (product A (product B C)) (associate pe A B C) =
      (Extension.Singleton.associateIso Join (G A) (G B) (G C)).hom
  map_unassociate (A B C : τ) :
    homEquiv (product A (product B C)) (product (product A B) C) (unassociate pe A B C) =
      (Extension.Singleton.associateIso Join (G A) (G B) (G C)).inv
  map_unitProjectionLeft (A : τ) :
    homEquiv (product unit A) A (productSnd pe unit A) = Extension.Singleton.unitProjectionLeft Join (G A)
  map_unitProjectionRight (A : τ) :
    homEquiv (product A unit) A (productFst pe A unit) = Extension.Singleton.unitProjectionRight Join (G A)
  map_leftUnitSection (A : τ) :
    homEquiv A (product unit A) (leftUnitSection pe A) =
      (Extension.Singleton.projection Join).map (Paper.TypeCategory.leftUnitSection A)
  map_rightUnitSection (A : τ) :
    homEquiv A (product A unit) (rightUnitSection pe A) =
      (Extension.Singleton.projection Join).map (Paper.TypeCategory.rightUnitSection A)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Operations
