module

public import Silmaril.Logic.TypeTheory.CIC.Semantics.Coherence.Thms
public import Silmaril.Logic.TypeTheory.CIC.Reduction.Thms

@[expose] public section

/-! # A staged operational extension of the concrete CIC evaluation kernel

The relation includes every canonical Evaluates derivation, including primitive
projections, and additionally admits compatible
trace application, unary constructor-directed fix/beta computation, and actual
tagged source iota reduction without constructor-local definitions. No fixed
trace or global soundness field is supplied. Lifting, substitution and the other
kernel transport laws for this relation are separate obligations.
-/

namespace Silmaril.Logic.TypeTheory.CIC.SetSemantics

universe u

/-- A finite operational derivation extends existing concrete values at explicit source computation rules. -/
inductive OperationalEvaluates (ρ : LevelName → ℕ) (universes : ℕ → Value.{u}) (globals : GlobalValues.{u}) :
    LocalValues.{u} → Expr → Value.{u} → Prop where
  | kernel {values term value} : Evaluates ρ universes globals values term value →
      OperationalEvaluates ρ universes globals values term value
  | application {values function argument f a} :
      OperationalEvaluates ρ universes globals values function f →
      OperationalEvaluates ρ universes globals values argument a →
      OperationalEvaluates ρ universes globals values (.app function argument) (traceApply f a)
  | fixBeta {values definitions index na domain body argument value} :
      unfoldFix definitions index = some (0, .lam na domain body) → Expr.IsConstructorApplication argument →
      OperationalEvaluates ρ universes globals values (body.subst [argument] 0) value →
      OperationalEvaluates ρ universes globals values (.app (.fix definitions index) argument) value
  | iota {values ci p scrutinee branches index ui arguments argumentValues branch value} :
      scrutinee = Expr.mkApps (.constructor ci.inductiveRef index ui) arguments →
      branches[index]? = some branch → (∀ declaration ∈ branch.context, declaration.value = none) →
      arguments.length = ci.parameterCount + branch.context.length →
      List.Forall₂ (Evaluates ρ universes globals values) arguments argumentValues →
      Evaluates ρ universes globals values scrutinee (constructorValue index argumentValues) →
      OperationalEvaluates ρ universes globals values (iotaReduce ci.parameterCount p arguments branch) value →
      OperationalEvaluates ρ universes globals values (.caseOf ci p scrutinee branches) value

end Silmaril.Logic.TypeTheory.CIC.SetSemantics
