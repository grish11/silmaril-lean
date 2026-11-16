module

public import Silmaril.Logic.TypeTheory.CIC.Reduction.Defs
public import Silmaril.Proofs.Logic.TypeTheory.CIC.Reduction

@[expose] public section

/-! # Operational CIC laws and binding examples -/

namespace Silmaril.Logic.TypeTheory.CIC

@[simp] theorem Context.subst_length (terms : List Expr) (cutoff : ℕ) (Γ : Context) :
    (Context.subst terms cutoff Γ).length = Γ.length :=
  Silmaril.Proofs.Logic.TypeTheory.CIC.ReductionLaws.context_subst_length terms cutoff Γ

@[simp] theorem Context.instantiate_length (ui : List Universe) (Γ : Context) :
    (Context.instantiate ui Γ).length = Γ.length :=
  Silmaril.Proofs.Logic.TypeTheory.CIC.ReductionLaws.context_instantiate_length ui Γ

@[simp] theorem Context.extendedSubst_length (Γ : Context) (n : ℕ) :
    (Γ.extendedSubst n).length = Γ.length :=
  Silmaril.Proofs.Logic.TypeTheory.CIC.ReductionLaws.extendedSubst_length Γ n

@[simp] theorem fixSubstitution_length (definitions : List (FixDef Expr)) :
    (fixSubstitution definitions).length = definitions.length :=
  Silmaril.Proofs.Logic.TypeTheory.CIC.ReductionLaws.fixSubstitution_length definitions

@[simp] theorem cofixSubstitution_length (definitions : List (FixDef Expr)) :
    (cofixSubstitution definitions).length = definitions.length :=
  Silmaril.Proofs.Logic.TypeTheory.CIC.ReductionLaws.cofixSubstitution_length definitions

@[simp] theorem fixContext_length (definitions : List (FixDef Expr)) :
    (fixContext definitions).length = definitions.length :=
  Silmaril.Proofs.Logic.TypeTheory.CIC.ReductionLaws.fixContext_length definitions

/-- Application spines compose by appending argument lists. -/
theorem Expr.mkApps_append (t : Expr) (as bs : List Expr) :
    Expr.mkApps t (as ++ bs) = Expr.mkApps (Expr.mkApps t as) bs :=
  Silmaril.Proofs.Logic.TypeTheory.CIC.ReductionLaws.mkApps_append t as bs

/-- Reduction is stable under any environment extension preserving constant lookup. -/
theorem Step.environment_mono {env env' : GlobalEnv}
    (hlookup : ∀ name decl, env.lookupConstant name = some decl →
      env'.lookupConstant name = some decl) {Γ : Context} {t u : Expr}
    (h : Step env Γ t u) : Step env' Γ t u :=
  Silmaril.Proofs.Logic.TypeTheory.CIC.ReductionLaws.step_environment_mono hlookup h

/-- The variable bound by an identity function is replaced by its actual argument. -/
theorem Step.beta_identity (env : GlobalEnv) (Γ : Context) (A argument : Expr) :
    Step env Γ (.app (.lam {} A (.rel 0)) argument) argument :=
  Silmaril.Proofs.Logic.TypeTheory.CIC.ReductionLaws.beta_identity env Γ A argument

/-- Iota expands a cached branch definition before consuming constructor arguments. -/
theorem iota_with_local_definition :
    iotaReduce 0
      { parameters := [], universeInstance := [], context := [], returnType := .sort .prop }
      [.free "argument"]
      { context := [
          { binder := {}, type := .free "T", value := some (.rel 0) },
          { binder := {}, type := .free "T" }], body := .rel 0 } = .free "argument" :=
  Silmaril.Proofs.Logic.TypeTheory.CIC.ReductionLaws.iota_with_local_definition

/-- The same branch-let example is an actual one-step case reduction. -/
theorem Step.iota_with_local_definition (env : GlobalEnv) (Γ : Context) :
    Step env Γ
      (.caseOf { inductiveRef := ⟨"I", 0⟩, parameterCount := 0, relevance := .relevant }
        { parameters := [], universeInstance := [], context := [], returnType := .sort .prop }
        (Expr.mkApps (.constructor ⟨"I", 0⟩ 0 []) [.free "argument"])
        [{ context := [
          { binder := {}, type := .free "T", value := some (.rel 0) },
          { binder := {}, type := .free "T" }], body := .rel 0 }])
      (.free "argument") :=
  Silmaril.Proofs.Logic.TypeTheory.CIC.ReductionLaws.iota_step_with_local_definition env Γ

/-- The second mutual declaration is nearest, and its type crosses the earlier declaration. -/
theorem fixContext_two :
    fixContext [
      { binder := {}, type := .rel 0, body := .rel 1, recursiveArgument := 0 },
      { binder := {}, type := .rel 0, body := .rel 0, recursiveArgument := 0 }] =
    [{ binder := {}, type := .rel 1 }, { binder := {}, type := .rel 0 }] :=
  Silmaril.Proofs.Logic.TypeTheory.CIC.ReductionLaws.fixContext_two

/-- The first member's self-reference has index one in a two-member block. -/
theorem unfoldFix_two (A B : Expr) :
    unfoldFix [
      { binder := {}, type := A, body := .rel 1, recursiveArgument := 0 },
      { binder := {}, type := B, body := .rel 0, recursiveArgument := 0 }] 0 =
    some (0, .fix [
      { binder := {}, type := A, body := .rel 1, recursiveArgument := 0 },
      { binder := {}, type := B, body := .rel 0, recursiveArgument := 0 }] 0) :=
  Silmaril.Proofs.Logic.TypeTheory.CIC.ReductionLaws.unfoldFix_two A B

/-- The second cofix member's self-reference has de Bruijn index zero. -/
theorem unfoldCofix_two (A B : Expr) :
    unfoldCofix [
      { binder := {}, type := A, body := .rel 1, recursiveArgument := 0 },
      { binder := {}, type := B, body := .rel 0, recursiveArgument := 0 }] 1 =
    some (0, .cofix [
      { binder := {}, type := A, body := .rel 1, recursiveArgument := 0 },
      { binder := {}, type := B, body := .rel 0, recursiveArgument := 0 }] 1) :=
  Silmaril.Proofs.Logic.TypeTheory.CIC.ReductionLaws.unfoldCofix_two A B

end Silmaril.Logic.TypeTheory.CIC
