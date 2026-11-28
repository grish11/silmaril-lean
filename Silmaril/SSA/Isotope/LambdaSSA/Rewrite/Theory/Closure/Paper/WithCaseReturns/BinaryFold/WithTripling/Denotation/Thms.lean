module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.Denotation.Tripling.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldWithTriplingDenotation

/-! # The canonical factorization of BinaryFold denotations -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling

open Silmaril.Isotope.LambdaSSA
open CategoryTheory CategoryTheory.Limits
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
  (ofRegion projection homRel)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "S" => JoinedStep (τ := τ) (Φ := Φ) pe
set_option hygiene false in
local notation "T" => Step (τ := τ) (Φ := Φ) pe
set_option hygiene false in
local notation "H" => fromBinaryFold (τ := τ) (Φ := Φ) pe

open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
  (SeedDenotes)

open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open scoped MonoidalCategory

universe u₁ u₂ v₁ v₂
variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J] (M : TypeModel τ V)
  [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]
  (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
    Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)

set_option hygiene false in
local notation "Old" => BinaryFold.denoteFunctor (Φ := Φ) pe J M shared

include shared in
/-- The exact feedback seed uses categorical uniformity for the ternary fold.
The existing BinaryFold seed keeps its original interpretation. -/
theorem seedDenotes : SeedDenotes (Seed := T) J M :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldWithTriplingDenotation.seedDenotes pe J M shared

/-- The same guarded denotation, descended through the opt-in quotient. -/
@[expose] noncomputable def denoteFunctor : TypeCategory (τ := τ) (Φ := Φ) pe ⥤ C :=
  Paper.Extension.Singleton.denoteFunctor J M shared (seedDenotes pe J M shared)

set_option hygiene false in
local notation "New" => denoteFunctor (Φ := Φ) pe J M shared

/-- The denotation agrees with BinaryFold on every old arrow. -/
theorem fromBinaryFold_comp_denoteFunctor : (H) ⋙ (New) = (Old) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldWithTriplingDenotation.fromBinaryFold_comp_denoteFunctor pe J M shared

/-- Each supported BinaryFold denotation factors uniquely as a functor
through the new quotient projection. -/
theorem existsUnique_denoteFactor :
    ∃! G : TypeCategory (τ := τ) (Φ := Φ) pe ⥤ C, (H) ⋙ G = (Old) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldWithTriplingDenotation.existsUnique_denoteFactor pe J M shared

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling
