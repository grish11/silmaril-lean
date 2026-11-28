module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.Denotation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedCallReturns.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Singleton.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Denotation.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingComputedCallDenotation

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Paper.WithCaseReturns.BinaryFold.WithTripling (Step denoteFunctor)
open Paper.Extension.Singleton (ofRegion)
open CfgEta.TypeCategory (returnRegion returnRegion_typed)

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
local notation "F" => denoteFunctor (Φ := Φ) pe J M shared

set_option backward.isDefEq.respectTransparency false in
private theorem map_eq_of_computedCallEqv {X D : τ} {r s : Region Φ}
    (hr : ValueBranches [X] r [D]) (hs : ValueBranches [X] s [D])
    (valid : Paper.Extension.Eqv Paper.WithComputedCallReturns.Step [X] r s [D]) :
    (F).map (ofRegion T hr) = (F).map (ofRegion T hs) := by
  unfold Paper.WithCaseReturns.BinaryFold.WithTripling.denoteFunctor
  rw [Paper.Extension.Singleton.denoteFunctor_map_ofRegion,
    Paper.Extension.Singleton.denoteFunctor_map_ofRegion]
  unfold denoteSingletonRegion
  rw [Paper.Extension.Eqv.sound J M shared (Paper.WithComputedCallReturns.step_denotes J M shared)
    valid hr.hasType hs.hasType]

private theorem root_eqv {X : τ} {a : Tm Φ} (p : Φ) (ha : Tm.HasType [X] a (instrSrc p)) :
    Paper.Extension.Eqv Paper.WithComputedCallReturns.Step [X]
      (returnRegion (.op p a)) (returnRegion (.let₁ a (.op p (.var 0)))) [instrTrg p] := by
  let root := Paper.WithComputedCallReturns.Step.seq p ha
  exact .extra root.valueBranches.1.hasType root.valueBranches.2.hasType root

theorem map_computedCall {X : τ} {a : Tm Φ} (p : Φ) (ha : Tm.HasType [X] a (instrSrc p)) :
    (F).map (ofRegion T (returnRegion_typed (.op ha))) =
      (F).map (ofRegion T
        (returnRegion_typed (.let₁ ha (.op (f := p) (.var (i := 0) rfl))))) :=
  map_eq_of_computedCallEqv pe J M shared _ _ (root_eqv p ha)

theorem map_computedCall_post {X D : τ} {a : Tm Φ}
    (p : Φ) (ha : Tm.HasType [X] a (instrSrc p)) {k : Nat → Region Φ}
    (hk : LSubst.ValueFamily [X] [instrTrg p] [D] k) :
    (F).map (ofRegion T ((returnRegion_typed (.op ha)).lsubst hk)) =
      (F).map (ofRegion T
        ((returnRegion_typed (.let₁ ha (.op (f := p) (.var (i := 0) rfl)))).lsubst hk)) :=
  map_eq_of_computedCallEqv pe J M shared _ _
    (.lsubstPost (root_eqv p ha) (returnRegion_typed (.op (f := p) ha))
      (returnRegion_typed (.let₁ ha (.op (f := p) (.var (i := 0) rfl))))
      (fun _ _ hi => (hk hi).hasType))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingComputedCallDenotation
