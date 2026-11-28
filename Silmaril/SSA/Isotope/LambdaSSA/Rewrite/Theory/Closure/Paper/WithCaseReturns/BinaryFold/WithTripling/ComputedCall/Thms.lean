module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.ComputedCall.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.Denotation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.ReturnFusion.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingComputedCallDenotation

/-! # Categorical validity on the original computed-call arrows -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling

open Silmaril Silmaril.Isotope.LambdaSSA
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Paper.Extension.Singleton (ofRegion)
open CfgEta.TypeCategory (returnRegion_typed)

universe u v w u₁ u₂ v₁ v₂
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)
  {V : Type u₁} {C : Type u₂}
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
local notation "T" => Step (τ := τ) (Φ := Φ) pe
local notation "F" => denoteFunctor pe J M shared

/-- Every supported denotation gives the same arrow for the typed computed
call and its explicit sequencing. The operand may be effectful. -/
theorem denoteFunctor_map_computedCall {X : τ} {a : Tm Φ}
    (p : Φ) (ha : Tm.HasType [X] a (instrSrc p)) :
    (F).map (ofRegion T (returnRegion_typed (.op ha))) =
      (F).map (ofRegion T
        (returnRegion_typed (.let₁ ha (.op (f := p) (.var (i := 0) rfl))))) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingComputedCallDenotation.map_computedCall pe J M shared p ha

/-- Validity survives a typed continuation that uses both the call result
and the captured source input. -/
theorem denoteFunctor_map_computedCall_post {X D : τ} {a : Tm Φ}
    (p : Φ) (ha : Tm.HasType [X] a (instrSrc p)) {k : Nat → Region Φ}
    (hk : LSubst.ValueFamily [X] [instrTrg p] [D] k) :
    (F).map (ofRegion T ((returnRegion_typed (.op ha)).lsubst hk)) =
      (F).map (ofRegion T
        ((returnRegion_typed (.let₁ ha (.op (f := p) (.var (i := 0) rfl)))).lsubst hk)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingComputedCallDenotation.map_computedCall_post
    pe J M shared p ha hk

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling
