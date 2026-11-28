module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.Denotation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Denotation.UniversalProperty.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingUniversalProperty

/-! # Interpretation on generated arrows and on the full singleton quotient -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling

open Silmaril.Isotope.LambdaSSA
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton (ofType)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.Generation

universe u v w u₁ u₂ v₁ v₂

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]
  (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
    Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)

set_option hygiene false in
local notation "T" => Step (τ := τ) (Φ := Φ) pe
local notation "Obj" => ofType T
local notation "instruction" => InstructionModel.denote (J := J) (M := M)
local notation "Interpretation" => Domain.Interpretation T (Coordinates.ofModel J M) instruction

/-- The supported target model already interprets the generated domain through
its specified type coordinates and primitive maps. -/
noncomputable def generatedInterpretation : Interpretation :=
  Paper.Extension.Singleton.generatedInterpretation J M shared (seedDenotes pe J M shared)

/-- A preserving functor on the generated domain has the unique natural
comparison with the canonical denotation in its specified coordinates. -/
theorem generatedInterpretation_universal (G : Interpretation) :
    ∃! e : (generatedInterpretation pe J M shared).functor ≅ G.functor, ∀ A : τ,
      e.hom.app (Domain.ofType T A) = (G.objIso A).inv :=
  Paper.Extension.Singleton.generatedInterpretation_universal J M shared (seedDenotes pe J M shared) G

/-- Coverage by the checked computation generators extends the same universal
property to the full quotient, for functors preserving those operations and
the given primitives. -/
theorem interpretation_universal_of_generated
    (allGenerated : ∀ {A B : τ} (f : Obj A ⟶ Obj B), Generated T f)
    (G : Paper.Extension.Singleton.TypeCategory T ⥤ C) (objIso : ∀ A : τ, G.obj (Obj A) ≅ J.obj (M.obj A))
    (hG : Preserves T G objIso (Coordinates.ofModel J M))
    (hp : ∀ p : Φ, mapInCoordinates T G objIso (primitive T p) = instruction p) :
    ∃! e : denoteFunctor (Φ := Φ) pe J M shared ≅ G,
      ∀ A : τ, e.hom.app (Obj A) = (objIso A).inv :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingUniversalProperty.interpretation_universal_of_generated
    pe J M shared allGenerated G objIso hG hp

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling
