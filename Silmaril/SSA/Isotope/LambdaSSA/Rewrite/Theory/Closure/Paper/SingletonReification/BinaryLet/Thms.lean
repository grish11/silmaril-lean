module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.BinaryLet.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.PackedBody.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedLet.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationBinaryLet

/-! # Literal binary let on packed singleton inputs -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.BinaryLet

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.DeBruijn (lift)
open Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (whiskerLeftRegion)
open Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedLet (diagonal returnOnce_typed)
open Silmaril.Isotope.LambdaSSA.Region.Paper.PackedBody (applyPacked)

universe u v

section Syntax

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {X A B D : τ} {a : Tm Φ} {p : Region Φ}

/-- Supply a packed body with the constructor record of the retained input and both components. -/
theorem applyPackedPair_typed (hp : ValueBranches [Silmaril.product X (Silmaril.product A B)] p [D]) :
    ValueBranches [B, A, X] (applyPackedPair p) [D] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationBinaryLet.applyPackedPair_typed hp

/-- The contextual product η law identifies destructuring the bound product with supplying the packed body directly. -/
theorem destructure_applyPackedPair (hp : ValueBranches [Silmaril.product X (Silmaril.product A B)] p [D]) :
    Paper.Eqv [Silmaril.product A B, X]
      (.let₂ (.var 0) ((applyPackedPair p).renameVars (lift (lift Nat.succ))))
      (applyPacked p) [D] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationBinaryLet.destructure_applyPackedPair hp

/-- The guarded product producer agrees with single-bind return for a product variable. -/
theorem returnPair_variable {i : Nat} (hi : At [X] i (Silmaril.product A B)) :
    Paper.Eqv [X] (returnPair (.var i : Tm Φ)) (Paper.RetainedLet.returnOnce (.var i))
      [Silmaril.product A B] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationBinaryLet.returnPair_variable hi

/-- The guarded product producer agrees with single-bind return for a constructor pair. -/
theorem returnPair_pair {l r : Tm Φ} (hl : Tm.BranchValue [X] l A) (hr : Tm.BranchValue [X] r B) :
    Paper.Eqv [X] (returnPair (.pair l r)) (Paper.RetainedLet.returnOnce (.pair l r))
      [Silmaril.product A B] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationBinaryLet.returnPair_pair hl hr

/-- Copy the input, run the guarded product producer while retaining the input, then run the packed body. -/
theorem literal_let₂ (ha : Tm.HasType [X] a (Silmaril.product A B))
    (hp : ValueBranches [Silmaril.product X (Silmaril.product A B)] p [D]) :
    Paper.Eqv [X]
      (compLSubst
        (compLSubst (fun _ => diagonal) (fun _ => whiskerLeftRegion (returnPair a)))
        (fun _ => p) 0)
      (.let₂ a (applyPackedPair p)) [D] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationBinaryLet.literal_let₂ ha hp

end Syntax

section Denotation

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory MonoidalCategory
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel bind_pre_map)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (extend)

universe u₁ u₂ v₁ v₂

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {X A B D : τ} {a : Tm Φ} {p : Region Φ}
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]

open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (extend)

/-- The literal packed binder transports the explicitly selected producer and
body witnesses, with both context reindexings written at their value types. -/
theorem literal_let₂_selected (ha : Tm.HasType [X] a (Silmaril.product A B))
    (hp : ValueBranches [Silmaril.product X (Silmaril.product A B)] p [D])
    {f : J.obj (ctxObj M [X]) ⟶ J.obj (M.obj (Silmaril.product A B))}
    {g : J.obj (ctxObj M [Silmaril.product X (Silmaril.product A B)]) ⟶ J.obj (labelObj M [D])}
    (df : Denotes J M ha f) (dg : RegionDenotes J M hp.hasType g) :
    RegionDenotes J M (.let₂ ha (applyPackedPair_typed hp).hasType)
      (extend J f ≫ J.map ((λ_ (M.obj X)).hom ▷ M.obj (Silmaril.product A B)) ≫
        J.map (M.productIso X (Silmaril.product A B)).inv ≫
        J.map (λ_ (M.obj (Silmaril.product X (Silmaril.product A B)))).inv ≫ g) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationBinaryLet.literal_let₂_selected J M ha hp df dg

variable [FreydCategory.CentralUnit J] [RegionTypingCoherent (Φ := Φ) J M]

/-- Single-bind return and destructure-and-rebuild evaluate the arbitrary scrutinee with the same effects. -/
theorem returnPair_denotation (ha : Tm.HasType [X] a (Silmaril.product A B)) :
    denoteSingletonRegion J M (returnPair_typed ha).hasType =
      denoteSingletonRegion J M (returnOnce_typed ha).hasType :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationBinaryLet.returnPair_denotation J M ha

/-- Literal binary let factors as retained evaluation followed by the original right-associated packed body. -/
theorem denote_literal_let₂ (ha : Tm.HasType [X] a (Silmaril.product A B))
    (hp : ValueBranches [Silmaril.product X (Silmaril.product A B)] p [D]) :
    denoteSingletonRegion J M (.let₂ ha (applyPackedPair_typed hp).hasType) =
      extend J (denoteSingletonRegion J M (returnPair_typed ha).hasType) ≫
        J.map (M.productIso X (Silmaril.product A B)).inv ≫ denoteSingletonRegion J M hp.hasType :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationBinaryLet.denote_literal_let₂ J M ha hp

end Denotation

end Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.BinaryLet
