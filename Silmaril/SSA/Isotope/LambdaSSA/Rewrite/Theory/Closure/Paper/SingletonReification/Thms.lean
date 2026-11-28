module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReification

/-! # Loop-free singleton reification -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (retainLeft)
open Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
open Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedLet (returnOnce_typed)
open Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedCase (reindexHom returnSum_typed)
open Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (productFstBranches productSndBranches)
open Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory.ConstructorReification (unitMap fstMap sndMap inlMap inrMap)

universe u v w u₃ v₃
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₃} [Category.{v₃} V] [CartesianMonoidalCategory V] [SymmetricCategory V]

section PackedBodyDenotation

universe u₄ v₄
variable {K : Type u₄} [Category.{v₄} K]
  [PremonoidalCategory K] [SymmetricPremonoidalCategory K]
  [HasFiniteCoproducts V] [HasFiniteCoproducts K]
  [DistributiveTensor V] [DistributivePremonoidalCategory K]
  [Iteration K] [ElgotCategory K] (J : V ⥤ K) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]

/-- Recover the exact environment and bound payload before running a packed body. -/
theorem denote_applyPacked [RegionTypingCoherent (Φ := Φ) J M]
    {X A D : τ} {p : Region Φ} (hp : ValueBranches [Silmaril.product X A] p [D]) :
    denoteRegion J M (Paper.PackedBody.applyPacked_typed hp).hasType ≫
        J.map (singletonLabelPayload M D) =
      J.map (((λ_ (M.obj X)).hom ▷ M.obj A) ≫ (M.productIso X A).inv) ≫
        denoteSingletonRegion J M hp.hasType :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReification.denote_applyPacked J M hp

end PackedBodyDenotation

set_option hygiene false in
local notation "C" => Paper.TypeCategory (τ := τ) Φ

variable
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]
  (objIso : ∀ T : τ, J.obj (M.obj T) ≅ ofType (Φ := Φ) T)
  {ε : Type w} [HasEff Φ ε] (pe : ε)

/-- The retained distributor is preserved by the whiskering and injection comparisons. -/
theorem distributor_compare (cmp : ModelComparisons J M objIso pe) (X A B : τ) :
    reindexHom J M objIso (J.map (CfgEta.TypeCategory.Retained.packedDistributor M X A B)) =
      ofRegion (τ := τ) (CfgEta.TypeCategory.Retained.distributorRegion_typed X A B) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReification.distributor_compare J M objIso pe cmp X A B

variable [FreydCategory.CentralUnit J] [RegionTypingCoherent (Φ := Φ) J M]
  {X D : τ} {r : Region Φ} {hr : ValueBranches [X] r [D]}

/-- Reify a packed loop-free singleton derivation as its exact Paper quotient arrow.
The distributor and diagonal comparisons follow from the premises. -/
theorem compare (cmp : ModelComparisons J M objIso pe) (h : LoopFree hr) :
    reindexHom J M objIso (denoteSingletonRegion J M hr.hasType) = ofRegion (τ := τ) hr :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReification.compare J M objIso pe cmp h

/-- Transfer reification to a branch-bound singleton with an explicit Paper equality to the representative. -/
theorem compare_of_eqv (cmp : ModelComparisons J M objIso pe)
    (shared : ∀ E S : V, ∃ h : J.obj E ⊗ J.obj S = J.obj (E ⊗ S),
      Functor.StrongPremonoidal.tensorIso (J := J) E S = eqToIso h)
    {s : Region Φ} (hs : ValueBranches [X] s [D]) (h : LoopFree hr) (e : Paper.Eqv [X] s r [D]) :
    reindexHom J M objIso (denoteSingletonRegion J M hs.hasType) = ofRegion (τ := τ) hs :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReification.compare_of_eqv J M objIso pe cmp shared hs h e

section BinaryLet

open Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.BinaryLet

variable {A B : τ} {a : Tm Φ} {p : Region Φ}

/-- Under the existing single-bind return comparison, agreement on the
guarded binary producer is equivalent to the displayed Paper equation. -/
theorem returnPair_comparison_iff (cmp : ModelComparisons J M objIso pe)
    (ha : Tm.HasType [X] a (Silmaril.product A B)) :
    (reindexHom J M objIso (denoteSingletonRegion J M (returnPair_typed ha).hasType) =
      ofRegion (τ := τ) (returnPair_typed ha)) ↔
      Paper.Eqv [X] (returnPair a) (Paper.RetainedLet.returnOnce a) [Silmaril.product A B] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReification.returnPair_comparison_iff
    J M objIso pe cmp ha

/-- Reify literal binary let from the packed body comparison. The guarded
binary producer is compared at its original scrutinee, using the displayed
equation. The retained input and both components use a right-associated
record. -/
theorem compare_let₂ (cmp : ModelComparisons J M objIso pe)
    (ha : Tm.HasType [X] a (Silmaril.product A B))
    (hp : ValueBranches [Silmaril.product X (Silmaril.product A B)] p [D])
    (hProducer : Paper.Eqv [X] (returnPair a) (Paper.RetainedLet.returnOnce a) [Silmaril.product A B])
    (hBody : reindexHom J M objIso (denoteSingletonRegion J M hp.hasType) = ofRegion (τ := τ) hp) :
    reindexHom J M objIso (denoteSingletonRegion J M (.let₂ ha (applyPackedPair_typed hp).hasType)) =
      ofRegion (τ := τ) (.let₂ ha (applyPackedPair_typed hp)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReification.compare_let₂
    J M objIso pe cmp ha hp hProducer hBody

end BinaryLet

end Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification
