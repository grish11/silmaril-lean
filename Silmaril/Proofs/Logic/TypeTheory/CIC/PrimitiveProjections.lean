module

public import Silmaril.Logic.TypeTheory.CIC.Semantics.Projections.Defs
import Mathlib.Tactic

public section

namespace Silmaril.Proofs.Logic.TypeTheory.CIC.PrimitiveProjectionLaws

open Silmaril.Logic.TypeTheory.CIC
open Silmaril.Logic.TypeTheory.CIC.SetSemantics

universe u

/-- A known record value has exactly the selected field, with no default for missing fields. -/
theorem evaluates_projection_iff {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}}
    {globals : GlobalValues.{u}} {values : LocalValues.{u}} {reference : ProjectionRef}
    {scrutinee : Expr} {arguments : List Value.{u}} {value : Value.{u}}
    (hs : Evaluates ρ universes globals values scrutinee (constructorValue 0 arguments)) :
    Evaluates ρ universes globals values (.projection reference scrutinee) value ↔
      arguments[reference.parameterCount + reference.argument]? = some value := by
  constructor
  · intro h
    cases h with
    | projection hs' hlookup =>
        have harguments := (constructorValue_inj.mp (evaluates_deterministic hs hs')).2
        cases harguments
        exact hlookup
  · exact Evaluates.projection hs

/-- Constructor tags other than zero cannot be projected by this primitive-record rule. -/
theorem evaluates_projection_wrong_tag {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}}
    {globals : GlobalValues.{u}} {values : LocalValues.{u}} {reference : ProjectionRef}
    {scrutinee : Expr} {index : ℕ} {arguments : List Value.{u}} {value : Value.{u}}
    (hs : Evaluates ρ universes globals values scrutinee (constructorValue index arguments))
    (hindex : index ≠ 0) : ¬ Evaluates ρ universes globals values (.projection reference scrutinee) value := by
  intro h
  cases h with
  | projection hs' _ =>
      exact hindex (constructorValue_inj.mp (evaluates_deterministic hs hs')).1

/-- Both endpoints of the actual source projection step evaluate to the same selected argument. -/
theorem projection_step_values {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}}
    {globals : GlobalValues.{u}} (env : GlobalEnv) (Γ : Context) {values : LocalValues.{u}}
    {reference : ProjectionRef} {ui : List Universe} {arguments : List Expr}
    {argumentValues : List Value.{u}} {argument : Expr}
    (hlookup : arguments[reference.parameterCount + reference.argument]? = some argument)
    (hargs : List.Forall₂ (Evaluates ρ universes globals values) arguments argumentValues)
    (hs : Evaluates ρ universes globals values
      (Expr.mkApps (.constructor reference.inductiveRef 0 ui) arguments) (constructorValue 0 argumentValues)) :
    Step env Γ (.projection reference (Expr.mkApps (.constructor reference.inductiveRef 0 ui) arguments)) argument ∧
      ∃ value, Evaluates ρ universes globals values
          (.projection reference (Expr.mkApps (.constructor reference.inductiveRef 0 ui) arguments)) value ∧
        Evaluates ρ universes globals values argument value := by
  have hbound := (List.getElem?_eq_some_iff.mp hlookup).1
  have hvbound : reference.parameterCount + reference.argument < argumentValues.length := hargs.length_eq ▸ hbound
  refine ⟨Step.project hlookup, argumentValues[reference.parameterCount + reference.argument],
    Evaluates.projection hs (List.getElem?_eq_getElem hvbound), ?_⟩
  simpa only [List.get_eq_getElem, (List.getElem?_eq_some_iff.mp hlookup).2] using hargs.get hbound hvbound

/-- All three actual constructor applications evaluate before the nonzero field/parameter offset is selected. -/
theorem projectionRegression_constructor_evaluates (ρ : LevelName → ℕ) (universes : ℕ → Value.{u})
    (P A B : Value.{u}) (p : P) (a : A) (b : B) :
    Evaluates ρ universes (projectionRegressionGlobals P A B) [b, a, p]
      projectionRegressionConstructor (constructorValue 0 [p, a, b]) := by
  have hc : Evaluates ρ universes (projectionRegressionGlobals P A B) [b, a, p]
      (.constructor projectionRegressionReference 0 [])
      (traceLambda P (fun p => traceLambda A (fun a => traceLambda B
        (fun b => constructorValue 0 [p, a, b])))) := by
    apply Evaluates.constructor
    simp only [projectionRegressionGlobals, and_self, ite_true]
  have hp : Evaluates ρ universes (projectionRegressionGlobals P A B) [b, a, p] (.rel 2) p := .rel rfl
  have ha : Evaluates ρ universes (projectionRegressionGlobals P A B) [b, a, p] (.rel 1) a := .rel rfl
  have hb : Evaluates ρ universes (projectionRegressionGlobals P A B) [b, a, p] (.rel 0) b := .rel rfl
  simpa only [projectionRegressionConstructor, Expr.mkApps, List.foldl_cons, List.foldl_nil, trace_beta] using
    Evaluates.application (Evaluates.application (Evaluates.application hc hp) ha) hb

/-- The source reduction, canonical value and operational value select field one after skipping its parameter. -/
theorem projectionRegression_values (ρ : LevelName → ℕ) (universes : ℕ → Value.{u})
    (P A B : Value.{u}) (p : P) (a : A) (b : B) (env : GlobalEnv) (Γ : Context) :
    Step env Γ (.projection ⟨projectionRegressionReference, 1, 1⟩ projectionRegressionConstructor) (.rel 0) ∧
      Evaluates ρ universes (projectionRegressionGlobals P A B) [b, a, p]
        (.projection ⟨projectionRegressionReference, 1, 1⟩ projectionRegressionConstructor) b ∧
      OperationalEvaluates ρ universes (projectionRegressionGlobals P A B) [b, a, p]
        (.projection ⟨projectionRegressionReference, 1, 1⟩ projectionRegressionConstructor) b := by
  have heval : Evaluates ρ universes (projectionRegressionGlobals P A B) [b, a, p]
      (.projection ⟨projectionRegressionReference, 1, 1⟩ projectionRegressionConstructor) b :=
    .projection (projectionRegression_constructor_evaluates ρ universes P A B p a b) rfl
  exact ⟨Step.project rfl, heval, .kernel heval⟩

/-- Projection evaluation composes through an actual nested field rather than only a local variable. -/
theorem evaluates_nested_projections {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}}
    {globals : GlobalValues.{u}} {values : LocalValues.{u}} {outer inner : ProjectionRef}
    {scrutinee : Expr} {arguments fields : List Value.{u}} {value : Value.{u}}
    (hs : Evaluates ρ universes globals values scrutinee (constructorValue 0 arguments))
    (houter : arguments[outer.parameterCount + outer.argument]? = some (constructorValue 0 fields))
    (hinner : fields[inner.parameterCount + inner.argument]? = some value) :
    Evaluates ρ universes globals values (.projection inner (.projection outer scrutinee)) value :=
  .projection (.projection hs houter) hinner

end Silmaril.Proofs.Logic.TypeTheory.CIC.PrimitiveProjectionLaws
