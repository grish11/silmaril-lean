module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseAndUnaryReturns.Denotation.UniversalProperty.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.StructuralValues.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Obstruction.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedCallReturns.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Tensor.Premonoidal.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.GeneratedReflection

/-! # Failure of model reflection for the generated case/unary domain

Cartesian value-unit terminality identifies two distinct generated arrows
already on the empty instruction signature.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseAndUnaryReturns

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open scoped BoundSimulation.Obstruction
open Extension.Singleton
open Extension.Singleton.Generation
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel)

universe u v u₁ u₂ v₁ v₂

local instance : HasEff Empty Bool := ⟨Empty.elim⟩
local notation "Seed" => Step (τ := Ty Empty) (Φ := Empty) false
local notation "U" => (Silmaril.unit : Ty Empty)

/-- Discard and identity at Unit are distinct in the generated case/unary domain. -/
theorem generated_discard_ne_id :
    Domain.discard Seed U ≠ 𝟙 (Domain.ofType Seed U) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.GeneratedReflection.generated_discard_ne_id

/-- The candidate structural value category fails terminality at its designated Unit. -/
theorem structural_unit_not_terminal :
    IsTerminal (⟨Extension.Singleton.ofType Seed U⟩ : StructuralValues.ValueCategory Seed) → False :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.GeneratedReflection.structural_unit_not_terminal

/-- The ordered-pair join includes the unit equation that identifies this witness. -/
theorem pair_join_discard_eq_id :
    let S := WithPairReturns.JoinedStep (τ := Ty Empty) (Φ := Empty) false
    Domain.discard S U = 𝟙 (Domain.ofType S U) :=
  WideSubcategory.hom_ext _ (unit_eta_of_include _ (fun h => .inl (.inl (.inr h))))

/-- The computed-call join inherits the unit equation from the ordered-pair join. -/
theorem computed_call_join_discard_eq_id :
    let S := WithComputedCallReturns.JoinedStep (τ := Ty Empty) (Φ := Empty) false
    Domain.discard S U = 𝟙 (Domain.ofType S U) :=
  WideSubcategory.hom_ext _ (unit_eta_of_include _ (fun h => .inl (.inl (.inl (.inr h)))))

section

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  [PremonoidalCategory C] [HasFiniteCoproducts C] [Iteration C]
  (J : V ⥤ C) [Functor.StrongPremonoidal J] [PreservesFiniteCoproducts J] (M : TypeModel τ V)

/-- A preserving interpretation in model coordinates sends discard at Unit to
identity. This uses only the discard law and terminality in the value category. -/
theorem interpretation_map_discard_unit
    {S : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}
    {instruction : ∀ p : Φ, J.obj (M.obj (instrSrc p)) ⟶ J.obj (M.obj (instrTrg p))}
    (I : Domain.Interpretation S (Coordinates.ofModel J M) instruction) :
    I.functor.map (Domain.discard S (Silmaril.unit : τ)) = 𝟙 _ :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.GeneratedReflection.interpretation_map_discard_unit J M I

/-- No interpretation of this generated domain in model coordinates can both
preserve the selected operations and be faithful. -/
theorem generated_interpretation_not_faithful
    (M : TypeModel (Ty Empty) V)
    {instruction : ∀ p : Empty, J.obj (M.obj (instrSrc p)) ⟶ J.obj (M.obj (instrTrg p))}
    (I : Domain.Interpretation Seed (Coordinates.ofModel J M) instruction) :
    ¬ I.functor.Faithful := by
  intro h
  exact generated_discard_ne_id (h.map_injective ((interpretation_map_discard_unit J M I).trans
    (I.functor.map_id _).symm))

end

open Silmaril.Isotope.LambdaSSA.Semantics.Categorical

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel (Ty Empty) V) [Silmaril.Isotope.LetIter.Semantics.Categorical.InstructionModel J M Empty]
  [RegionTypingCoherent (Φ := Empty) J M]
  (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
    Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)

/-- The same two generated arrows have equal images in every coherent
shared-tensor model for the case/unary theory. -/
theorem generatedInterpretation_map_discard_unit :
    (generatedInterpretation (Φ := Empty) false J M shared).functor.map (Domain.discard Seed U) =
      (generatedInterpretation (Φ := Empty) false J M shared).functor.map (𝟙 (Domain.ofType Seed U)) :=
  (interpretation_map_discard_unit J M _).trans ((generatedInterpretation (Φ := Empty) false J M shared).functor.map_id _).symm

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseAndUnaryReturns
