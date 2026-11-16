module

public import Silmaril.Logic.TypeTheory.CIC.Semantics.Instantiation.Defs
public import Silmaril.Logic.TypeTheory.CIC.Semantics.Local.Thms
public import Silmaril.Logic.TypeTheory.CIC.Universes.Thms
import Mathlib.Tactic

public section

namespace Silmaril.Proofs.Logic.TypeTheory.CIC.UniverseEvaluationLaws

open Silmaril.Logic.TypeTheory.CIC
open Silmaril.Logic.TypeTheory.CIC.SetSemantics

universe u

/-- Evaluating a substituted sort agrees with composing the valuation. -/
theorem sortValue_substUniverses (σ : LevelName → Universe) (ρ : LevelName → ℕ)
    (universes : ℕ → Value.{u}) (s : SortExpr LevelName) :
    sortValue ρ universes (s.map (UniverseExpr.subst σ)) =
      sortValue (fun level => (σ level).eval ρ) universes s := by
  cases s <;> simp [sortValue, SortExpr.map]

/-- Actual CIC universe substitution preserves values under valuation composition and explicit global reindexing. -/
theorem evaluates_substUniverses {σ : LevelName → Universe} {ρ : LevelName → ℕ}
    {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    {values : LocalValues.{u}} {term : Expr} {value : Value.{u}}
    (h : Evaluates (fun level => (σ level).eval ρ) universes (globals.pullbackUniverses σ) values term value) :
    Evaluates ρ universes globals values (term.substUniverses σ) value := by
  induction h with
  | rel hlookup => simpa only [Term.substUniverses] using (Evaluates.rel hlookup)
  | @sort values sort =>
      simpa only [Term.substUniverses, sortValue_substUniverses] using
        (Evaluates.sort (ρ := ρ) (universes := universes) (globals := globals) (values := values)
          (sort := sort.map (UniverseExpr.subst σ)))
  | product hA hB ihA ihB =>
      simpa only [Term.substUniverses] using Evaluates.product ihA ihB
  | lambda hA hf ihA ihf =>
      simpa only [Term.substUniverses] using Evaluates.lambda ihA ihf
  | application hf ha ihf iha =>
      simpa only [Term.substUniverses] using Evaluates.application ihf iha
  | letIn ha hb iha ihb =>
      simpa only [Term.substUniverses] using Evaluates.letIn iha ihb
  | @constant values name ui value hlookup =>
      have htarget : globals.constant name (ui.map (UniverseExpr.subst σ)) = some value := hlookup
      simpa only [Term.substUniverses] using
        (Evaluates.constant (ρ := ρ) (universes := universes) (values := values) htarget)
  | @inductiveType values reference ui value hlookup =>
      have htarget : globals.inductiveType reference (ui.map (UniverseExpr.subst σ)) = some value := hlookup
      simpa only [Term.substUniverses] using
        (Evaluates.inductiveType (ρ := ρ) (universes := universes) (values := values) htarget)
  | @constructor values reference index ui value hlookup =>
      have htarget : globals.constructor reference index (ui.map (UniverseExpr.subst σ)) = some value := hlookup
      simpa only [Term.substUniverses] using
        (Evaluates.constructor (ρ := ρ) (universes := universes) (values := values) htarget)
  | @caseOf values ci p scrutinee branches index arguments branch value hs hlookup hnone hlength hb ihs ihb =>
      simp only [Term.substUniverses]
      let substituted : Branch Expr := { branch with body := branch.body.substUniverses σ }
      have hselected : (branches.map (fun b => { b with body := b.body.substUniverses σ }))[index]? = some substituted := by
        simp only [List.getElem?_map, hlookup, Option.map_some]
        rfl
      exact Evaluates.caseOf (branch := substituted) ihs hselected hnone hlength ihb

  | projection hs hlookup ihs =>
      simpa only [Term.substUniverses] using Evaluates.projection ihs hlookup

/-- A term and its syntactic type retain their actual inhabitation after universe substitution. -/
theorem hasValueAt_substUniverses {σ : LevelName → Universe} {ρ : LevelName → ℕ}
    {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    {values : LocalValues.{u}} {term type : Expr}
    (h : HasValueAt (fun level => (σ level).eval ρ) universes (globals.pullbackUniverses σ) values term type) :
    HasValueAt ρ universes globals values (term.substUniverses σ) (type.substUniverses σ) := by
  obtain ⟨value, A, hterm, htype, hmember⟩ := h
  exact ⟨value, A, evaluates_substUniverses hterm, evaluates_substUniverses htype, hmember⟩

/-- Universe substitution on actual local declaration types and bodies retains the same realizing local values. -/
theorem interpretsLocal_substUniverses {σ : LevelName → Universe} {ρ : LevelName → ℕ}
    {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}} {Γ : Context} {values : LocalValues.{u}}
    (h : InterpretsLocal (fun level => (σ level).eval ρ) universes (globals.pullbackUniverses σ) Γ values) :
    InterpretsLocal ρ universes globals (Γ.map (ContextDecl.mapTerms (Term.substUniverses σ))) values := by
  induction h with
  | nil => exact InterpretsLocal.nil
  | assumption hΓ hA ha ih =>
      exact InterpretsLocal.assumption ih (evaluates_substUniverses hA) ha
  | definition hΓ hA hvalue ha ih =>
      exact InterpretsLocal.definition ih (evaluates_substUniverses hA) (evaluates_substUniverses hvalue) ha

/-- Raw universe-instance evaluation coherence; typing separately checks instance length, scope and constraints. -/
theorem evaluates_instantiate (ui : List Universe) {ρ : LevelName → ℕ}
    {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    {values : LocalValues.{u}} {term : Expr} {value : Value.{u}}
    (h : Evaluates (fun level => (instanceSubstitution ui level).eval ρ) universes
      (globals.pullbackUniverses (instanceSubstitution ui)) values term value) :
    Evaluates ρ universes globals values (Expr.instantiate ui term) value :=
  evaluates_substUniverses h

/-- Inhabitation is retained by the actual declaration universe-instance operation. -/
theorem hasValueAt_instantiate (ui : List Universe) {ρ : LevelName → ℕ}
    {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    {values : LocalValues.{u}} {term type : Expr}
    (h : HasValueAt (fun level => (instanceSubstitution ui level).eval ρ) universes
      (globals.pullbackUniverses (instanceSubstitution ui)) values term type) :
    HasValueAt ρ universes globals values (Expr.instantiate ui term) (Expr.instantiate ui type) :=
  hasValueAt_substUniverses h

/-- Declaration-context instantiation retains actual local realizations under the corresponding valuation. -/
theorem interpretsLocal_instantiate (ui : List Universe) {ρ : LevelName → ℕ}
    {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}} {Γ : Context} {values : LocalValues.{u}}
    (h : InterpretsLocal (fun level => (instanceSubstitution ui level).eval ρ) universes
      (globals.pullbackUniverses (instanceSubstitution ui)) Γ values) :
    InterpretsLocal ρ universes globals (Context.instantiate ui Γ) values :=
  interpretsLocal_substUniverses h


/-- A genuinely substituted parameter sort denotes the universe selected by its actual instance argument. -/
theorem instantiated_parameter_sort (level : Universe) (ρ : LevelName → ℕ)
    (universes : ℕ → Value.{u}) (globals : GlobalValues.{u}) :
    Evaluates ρ universes globals []
      (Expr.instantiate [level] (.sort (.type (.level (.parameter 0))))) (universes (level.eval ρ)) := by
  have hsource : Evaluates (fun name => (instanceSubstitution [level] name).eval ρ) universes
      (globals.pullbackUniverses (instanceSubstitution [level])) []
      (.sort (.type (.level (.parameter 0)))) (universes (level.eval ρ)) := by
    simpa only [sortValue, UniverseExpr.eval, instanceSubstitution, List.getElem?_cons_zero, Option.getD_some] using
      (Evaluates.sort (ρ := fun name => (instanceSubstitution [level] name).eval ρ)
        (universes := universes) (globals := globals.pullbackUniverses (instanceSubstitution [level]))
        (values := []) (sort := .type (.level (.parameter 0))))
  exact evaluates_instantiate [level] hsource

end Silmaril.Proofs.Logic.TypeTheory.CIC.UniverseEvaluationLaws
