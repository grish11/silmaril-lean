module

public import Silmaril.Logic.TypeTheory.CIC.Reduction.Defs
public import Silmaril.Logic.TypeTheory.CIC.Syntax.Thms
import Mathlib.Tactic

public section

namespace Silmaril.Proofs.Logic.TypeTheory.CIC.ReductionLaws

open Silmaril.Logic.TypeTheory.CIC

@[simp] theorem context_subst_length (terms : List Expr) (cutoff : ℕ) (Γ : Context) :
    (Context.subst terms cutoff Γ).length = Γ.length := by
  simp [Context.subst, Context.mapAt]

@[simp] theorem context_instantiate_length (ui : List Universe) (Γ : Context) :
    (Context.instantiate ui Γ).length = Γ.length := by
  simp [Context.instantiate]

@[simp] theorem extendedSubst_length (Γ : Context) (n : ℕ) :
    (Γ.extendedSubst n).length = Γ.length := by
  induction Γ generalizing n with
  | nil => rfl
  | cons d Γ ih => cases h : d.value <;> simp [Context.extendedSubst, h, ih]

@[simp] theorem fixSubstitution_length (definitions : List (FixDef Expr)) :
    (fixSubstitution definitions).length = definitions.length := by
  simp [fixSubstitution]

@[simp] theorem cofixSubstitution_length (definitions : List (FixDef Expr)) :
    (cofixSubstitution definitions).length = definitions.length := by
  simp [cofixSubstitution]

@[simp] theorem fixContext_length (definitions : List (FixDef Expr)) :
    (fixContext definitions).length = definitions.length := by
  simp [fixContext]

theorem mkApps_append (t : Expr) (as bs : List Expr) :
    Expr.mkApps t (as ++ bs) = Expr.mkApps (Expr.mkApps t as) bs := by
  simp [Expr.mkApps, List.foldl_append]

theorem beta_identity (env : GlobalEnv) (Γ : Context) (A argument : Expr) :
    Step env Γ (.app (.lam {} A (.rel 0)) argument) argument := by
  simpa [Term.subst] using
    (Step.beta (env := env) (Γ := Γ) (na := {}) (A := A) (body := .rel 0) (argument := argument))

theorem iota_with_local_definition :
    iotaReduce 0
      { parameters := [], universeInstance := [], context := [], returnType := .sort .prop }
      [.free "argument"]
      { context := [
          { binder := {}, type := .free "T", value := some (.rel 0) },
          { binder := {}, type := .free "T" }], body := .rel 0 } = .free "argument" := by
  simp [iotaReduce, Context.instantiateCase, Context.instantiate, Context.subst,
    Context.mapAt, ContextDecl.mapTerms, Expr.instantiate, Term.substUniverses,
    Context.expandLets, Context.assumptionCount, Context.extendedSubst, Term.lift, Term.subst]

theorem iota_step_with_local_definition (env : GlobalEnv) (Γ : Context) :
    Step env Γ
      (.caseOf { inductiveRef := ⟨"I", 0⟩, parameterCount := 0, relevance := .relevant }
        { parameters := [], universeInstance := [], context := [], returnType := .sort .prop }
        (Expr.mkApps (.constructor ⟨"I", 0⟩ 0 []) [.free "argument"])
        [{ context := [
          { binder := {}, type := .free "T", value := some (.rel 0) },
          { binder := {}, type := .free "T" }], body := .rel 0 }])
      (.free "argument") := by
  simpa only [iota_with_local_definition] using
    (Step.iota (env := env) (Γ := Γ)
      (ci := { inductiveRef := ⟨"I", 0⟩, parameterCount := 0, relevance := .relevant })
      (index := 0) (ui := []) (args := [.free "argument"])
      (p := { parameters := [], universeInstance := [], context := [], returnType := .sort .prop })
      (branches := [{ context := [
        { binder := {}, type := .free "T", value := some (.rel 0) },
        { binder := {}, type := .free "T" }], body := .rel 0 }])
      (branch := { context := [
        { binder := {}, type := .free "T", value := some (.rel 0) },
        { binder := {}, type := .free "T" }], body := .rel 0 }) rfl rfl)

theorem fixContext_two :
    fixContext [
      { binder := {}, type := .rel 0, body := .rel 1, recursiveArgument := 0 },
      { binder := {}, type := .rel 0, body := .rel 0, recursiveArgument := 0 }] =
    [{ binder := {}, type := .rel 1 }, { binder := {}, type := .rel 0 }] := by
  simp [fixContext, Term.lift]

theorem unfoldFix_two (A B : Expr) :
    unfoldFix [
      { binder := {}, type := A, body := .rel 1, recursiveArgument := 0 },
      { binder := {}, type := B, body := .rel 0, recursiveArgument := 0 }] 0 =
    some (0, .fix [
      { binder := {}, type := A, body := .rel 1, recursiveArgument := 0 },
      { binder := {}, type := B, body := .rel 0, recursiveArgument := 0 }] 0) := by
  simp [unfoldFix, fixSubstitution, Term.subst]

theorem unfoldCofix_two (A B : Expr) :
    unfoldCofix [
      { binder := {}, type := A, body := .rel 1, recursiveArgument := 0 },
      { binder := {}, type := B, body := .rel 0, recursiveArgument := 0 }] 1 =
    some (0, .cofix [
      { binder := {}, type := A, body := .rel 1, recursiveArgument := 0 },
      { binder := {}, type := B, body := .rel 0, recursiveArgument := 0 }] 1) := by
  simp [unfoldCofix, cofixSubstitution, Term.subst]

theorem step_environment_mono {env env' : GlobalEnv}
    (hlookup : ∀ name decl, env.lookupConstant name = some decl →
      env'.lookupConstant name = some decl) {Γ : Context} {t u : Expr}
    (h : Step env Γ t u) : Step env' Γ t u := by
  induction h <;> first
  | exact Step.cofixCase (by assumption)
  | exact Step.cofixProjection (by assumption)
  | aesop (add safe constructors Step)

end Silmaril.Proofs.Logic.TypeTheory.CIC.ReductionLaws
