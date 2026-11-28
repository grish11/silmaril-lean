module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.StructuralValues.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Denotation.Preservation.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldDenotationTripling

/-! # The pure phase fold in BinaryFold interpretations -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

universe u v w u₁ u₂ v₁ v₂
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J] (M : TypeModel τ V)
  [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]
  (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
    Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)

open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.StructuralValues (inclusion)

set_option hygiene false in
local notation "S" => JoinedStep (τ := τ) (Φ := Φ) pe
set_option hygiene false in
local notation "Obj" => ofType S
set_option hygiene false in
local notation "Q" => Paper.Extension.Singleton.TypeCategory S
set_option hygiene false in
local notation "I" => iterateChosen S
local infixr:65 " ⊕ₜ " => Silmaril.coprod

include shared in
/-- Each extra BinaryFold generator has a common denotation at both typed endpoints. -/
theorem seedDenotes : SeedDenotes (Seed := S) J M := by
  intro Γ r s L seed hr hs
  have eq := Eqv.sound pe J M shared (.extra hr hs seed) hr hs
  exact ⟨_, denoteRegion_spec J M hr, eq.symm ▸ denoteRegion_spec J M hs⟩

/-- The existing guarded categorical denotation descends through BinaryFold. -/
@[expose] noncomputable def denoteFunctor : Q ⥤ C :=
  Paper.Extension.Singleton.denoteFunctor J M shared (seedDenotes pe J M shared)

set_option hygiene false in
local notation "F" => denoteFunctor pe J M shared

/-- The exact three-copy fold is the image of the value copair of three
identities, including for a payload with an arbitrary interpreted base type. -/
theorem denoteFunctor_map_ternaryFold (A : τ) :
    (F).map ((inclusion S).map (ternaryFold pe A)) =
      J.map ((M.coprodIso A (A ⊕ₜ A)).hom ≫
        coprod.desc (𝟙 (M.obj A)) ((M.coprodIso A A).hom ≫ coprod.desc (𝟙 (M.obj A)) (𝟙 (M.obj A)))) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldDenotationTripling.map_ternaryFold pe J M shared (seedDenotes pe J M shared) A

/-- The computation images of the two exact feedback arrows obey the
uniformity equation for the pure three-copy fold. -/
theorem denoteFunctor_map_ternary_uniformity {A B : τ} (g : Obj A ⟶ Obj B ⨿ Obj A) :
    (F).map (I (ternaryStep pe g)) =
      (F).map ((inclusion S).map (ternaryFold pe A)) ≫ (F).map (I g) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldDenotationTripling.map_ternary_uniformity
    pe J M shared (seedDenotes pe J M shared) g

/-- Pure-map uniformity in the supported categorical model class forces
tripling at each exact BinaryFold state and outward type. -/
theorem denoteFunctor_map_tripling {A B : τ} (g : Obj A ⟶ Obj B ⨿ Obj A) :
    (F).map (I (ThreeCycle.triple g)) = (F).map (I g) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldDenotationTripling.map_tripling pe J M shared (seedDenotes pe J M shared) g

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold
