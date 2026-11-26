module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProductDestructureReturns.BranchBinding.Comparison.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.Singleton.Iteration.Thms

/-! # Product-destructuring raw singletons and the change-of-seed square -/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProductDestructureReturns.BranchBinding

open CategoryTheory
open Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding
open Paper.Extension.Singleton (ofType)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

/-- The stronger raw relation uses the existing product join with branch binding. -/
def singletonSeed : Singleton.NormalizedSeed τ Φ where
  step := JoinedStep pe
  eqv_iff_normalized hr hs := joined_eqv_iff_normalized pe hr hs

local notation "ProductSeed" => singletonSeed (τ := τ) (Φ := Φ) pe
local notation "ProductJoin" => JoinedStep (τ := τ) (Φ := Φ) pe
local notation "PairJoin" => WithPairReturns.JoinedStep (τ := τ) (Φ := Φ) pe
local notation "OldRaw" => OrderedPairSingleton.RawTypeCategory (τ := τ) Φ pe
local notation "NewRaw" => Singleton.RawTypeCategory ProductSeed

/-- The exact hom equivalence for the stronger raw and guarded quotients. -/
noncomputable abbrev singletonHomEquiv (A B : τ) :
    Singleton.RawHom ProductSeed A B ≃ (ofType ProductJoin A ⟶ ofType ProductJoin B) :=
  Singleton.homEquiv ProductSeed A B

/-- The same comparison is a strict category isomorphism. -/
noncomputable abbrev singletonCategoryIso :
    Cat.of NewRaw ≅ Cat.of (Extension.Singleton.TypeCategory ProductJoin) :=
  Singleton.categoryIso ProductSeed

/-- Change the raw seed while keeping the same literal representative. -/
def orderedPairRawMap {A B : τ} (f : OrderedPairSingleton.RawHom (Φ := Φ) pe A B) :
    Singleton.RawHom ProductSeed A B :=
  Quotient.map id (fun _ _ h => mapSeed
    (fun h => h.elim (fun h => .inl (.inl (.inl h))) Or.inr) h) f

/-- The old raw quotient projects functorially to the stronger raw quotient. -/
def orderedPairRawProjection : OldRaw ⥤ NewRaw where
  obj X := ⟨X.as⟩
  map f := orderedPairRawMap pe f
  map_id _ := rfl
  map_comp f g := Quotient.inductionOn₂ f g (fun _ _ => rfl)

/-- Changing the seed before normalization agrees with projecting the
normalized guarded arrow. Both routes keep the same syntax types. -/
theorem singleton_normalization_square :
    orderedPairRawProjection pe ⋙ Singleton.normalizeFunctor ProductSeed =
      normalizeFromOrderedPair pe := by
  refine Functor.hext (fun _ => rfl) (fun _ _ f => ?_)
  exact Quotient.inductionOn f (fun _ => HEq.rfl)

theorem orderedPairRawMap_iterateSum {A B : τ}
    (f : OrderedPairSingleton.RawHom (Φ := Φ) pe A (coprod B A)) :
    orderedPairRawMap pe (OrderedPairSingleton.iterateSum pe f) =
      Singleton.iterateSum ProductSeed (orderedPairRawMap pe f) :=
  Quotient.inductionOn f (fun _ => rfl)

/-- The guarded projection in the same square preserves exact-sum feedback. -/
theorem orderedPairProjection_iterateSum {A B : τ}
    (f : ofType PairJoin A ⟶ ofType PairJoin (coprod B A)) :
    (orderedPairProjection pe).map (Extension.Singleton.iterateSum PairJoin f) =
      Extension.Singleton.iterateSum ProductJoin ((orderedPairProjection pe).map f) := by
  induction f using Quot.ind with
  | _ f => rfl

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProductDestructureReturns.BranchBinding
