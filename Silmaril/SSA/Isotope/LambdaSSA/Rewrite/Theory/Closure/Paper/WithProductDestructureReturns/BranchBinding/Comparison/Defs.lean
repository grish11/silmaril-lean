module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProductDestructureReturns.BranchBinding.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Thms

/-! # Change of seed from ordered pairs to product-destructuring returns -/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProductDestructureReturns.BranchBinding

open Silmaril CategoryTheory
open Paper.Extension.Singleton (homRel projection ofRegion_eq_iff)
open Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding (mapSeed)
open Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton
  (RawTypeCategory normalizeFunctor)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

local notation "Pair" => WithPairReturns.JoinedStep (τ := τ) (Φ := Φ) pe
local notation "ProductJoin" => JoinedStep (τ := τ) (Φ := Φ) pe

/-- Include the old equations into the stronger guarded singleton quotient. -/
def orderedPairProjection : Extension.Singleton.TypeCategory Pair ⥤ Extension.Singleton.TypeCategory ProductJoin :=
  CategoryTheory.Quotient.lift (homRel Pair) (projection ProductJoin) fun _ _ _ _ h => by
    obtain ⟨r, s, hr, hs, rfl, rfl, e⟩ := h
    exact (ofRegion_eq_iff ProductJoin hr hs).mpr (mapSeed (fun h => .inl (.inl h)) e)

/-- Normalize with the existing ordered-pair raw operations, then pass to the stronger guarded quotient. -/
def normalizeFromOrderedPair : RawTypeCategory (τ := τ) Φ pe ⥤ Extension.Singleton.TypeCategory ProductJoin :=
  normalizeFunctor pe ⋙ orderedPairProjection pe

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProductDestructureReturns.BranchBinding
