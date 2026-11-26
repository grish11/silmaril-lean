module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseAndUnaryReturns.Denotation.UniversalProperty.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.StructuralValues.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Obstruction.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.CaseReturns

/-! # Terminality and generated-arrow reflection -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.GeneratedReflection

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Paper.Extension.Singleton
open Paper.Extension.Singleton.Generation
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer (Env EnvTy Result)
open PairSequencing (caseReturnSeed_same)
open scoped Paper.BoundSimulation.Obstruction

universe u v w x y z

local instance : HasEff Empty Bool := ⟨Empty.elim⟩
local notation "Seed" => Paper.WithCaseAndUnaryReturns.Step (τ := Ty Empty) (Φ := Empty) false
local notation "U" => (Silmaril.unit : Ty Empty)

open scoped Observer.AlternateUnit in
private theorem unit_eta_fails :
    ¬ Paper.Extension.Eqv Seed [U] (.br 0 .unit) (.br 0 (.var 0)) [U] := by
  intro h
  let env : Env := fun _ => .inl .unit
  have henv : EnvTy [U] env := by
    intro i A hi
    cases i with
    | zero => cases Option.some.inj hi; exact .alternateUnit rfl
    | succ i => simp [At] at hi
  have observed := PairSequencing.Observer.extension_same (observation := {})
    (fun e => e.elim PairSequencing.Observer.unary_fusion_same (caseReturnSeed_same rfl)) h env henv
  change Result.jump 0 .unit = Result.jump 0 (.inl .unit) at observed
  cases observed

private theorem discard_ne_id :
    Paper.Extension.Singleton.discardArrow Seed U ≠ 𝟙 (Paper.Extension.Singleton.ofType Seed U) := by
  intro h
  rw [← (projection Seed).map_id, ← Paper.TypeCategory.ofRegion_id (Φ := Empty)] at h
  exact unit_eta_fails ((ofRegion_eq_iff Seed _ _).1 h)

theorem generated_discard_ne_id :
    Domain.discard Seed U ≠ 𝟙 (Domain.ofType Seed U) := fun h =>
  discard_ne_id (congrArg (generatedInclusion Seed).map h)

theorem structural_unit_not_terminal :
    IsTerminal (⟨Paper.Extension.Singleton.ofType Seed U⟩ : StructuralValues.ValueCategory Seed) → False := by
  intro terminal
  let d : (⟨Paper.Extension.Singleton.ofType Seed U⟩ : StructuralValues.ValueCategory Seed) ⟶
      (⟨Paper.Extension.Singleton.ofType Seed U⟩ : StructuralValues.ValueCategory Seed) :=
    ⟨_, StructuralValues.branch_mem Seed (.unit (Γ := [U]))⟩
  exact discard_ne_id (congrArg (StructuralValues.inclusion Seed).map (terminal.hom_ext d (𝟙 _)))

open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel)
open CfgEta.TypeCategory.ConstructorReification (unitMap)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type w} {C : Type x} [Category.{y} V] [Category.{z} C]
  [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  [PremonoidalCategory C] [HasFiniteCoproducts C] [Iteration C]
  (J : V ⥤ C) [Functor.StrongPremonoidal J] [PreservesFiniteCoproducts J] (M : TypeModel τ V)

set_option backward.isDefEq.respectTransparency false in
theorem interpretation_map_discard_unit
    {S : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}
    {instruction : ∀ p : Φ, J.obj (M.obj (instrSrc p)) ⟶ J.obj (M.obj (instrTrg p))}
    (I : Domain.Interpretation S (Coordinates.ofModel J M) instruction) :
    I.functor.map (Domain.discard S (Silmaril.unit : τ)) = 𝟙 _ := by
  let A : τ := Silmaril.unit
  have h : unitMap M A = 𝟙 (M.obj A) :=
    (cancel_mono M.unitIso.hom).mp (Subsingleton.elim _ _)
  have discard := I.discard A
  change Domain.mapInCoordinates S I.functor I.objIso (Domain.discard S A) = J.map (unitMap M A) at discard
  rw [h, J.map_id] at discard
  change I.functor.map (Domain.discard S A) = 𝟙 _
  rw [← cancel_epi (I.objIso A).inv, ← cancel_mono (I.objIso A).hom]
  simpa [Domain.mapInCoordinates, Category.assoc] using discard

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.GeneratedReflection
