module

public import Silmaril.Languages.Python.Compile.Closed.Defs
import Silmaril.Proofs.Languages.Python.Compile.Closed.Thms

public section
namespace Silmaril.Proofs.Languages.Python.Compile.Closed

open Silmaril.Languages.Python
open Silmaril.Languages.Python.Compile.Closed

private theorem lowerExpr_error {source : Source.Expr} {error : Error}
    (failed : lowerExpr source = .error error) : error = .expressionShape := by
  cases source <;> try solve | (simp [lowerExpr] at failed; exact failed.symm)
  case integer value => simp [lowerExpr] at failed
  case binary operator left right =>
    cases operator <;> try solve | (simp [lowerExpr] at failed; exact failed.symm)
    case add =>
      cases lhs : lowerExpr left with
      | error diagnostic =>
        simp [lowerExpr, Except.bind, lhs] at failed
        subst error
        exact lowerExpr_error lhs
      | ok expr =>
        cases rhs : lowerExpr right with
        | error diagnostic =>
          simp [lowerExpr, Except.bind, Except.map, lhs, rhs] at failed
          subst error
          exact lowerExpr_error rhs
        | ok expr => simp [lowerExpr, Except.bind, Except.map, lhs, rhs] at failed
termination_by sizeOf source

private theorem lower_bad_module (source : Source.Module) :
    lower source = .error .moduleShape ↔ ¬ ModuleShape source := by
  constructor
  · intro failed
    rintro ⟨name, value, rfl⟩
    cases lowered : lowerExpr value with
    | ok expr => simp [lower, Except.map, lowered] at failed
    | error diagnostic =>
      simp [lower, Except.map, lowered] at failed
      subst diagnostic
      cases lowerExpr_error lowered
  · intro missing
    unfold lower
    split
    next name value => exact False.elim (missing ⟨name, value, rfl⟩)
    next => rfl

private theorem lower_bad_expression (source : Source.Module) :
    lower source = .error .expressionShape ↔
      ModuleShape source ∧ ¬ ∃ target, Translation source target := by
  constructor
  · intro failed
    refine ⟨?_, ?_⟩
    · by_contra missing
      have wrong := (lower_bad_module source).mpr missing
      rw [failed] at wrong
      cases wrong
    · rintro ⟨target, translated⟩
      have accepted := (lower_iff source target).mpr translated
      rw [failed] at accepted
      cases accepted
  · rintro ⟨⟨name, value, rfl⟩, unsupported⟩
    cases lowered : lowerExpr value with
    | error diagnostic =>
      simp [lower, Except.map, lowered, lowerExpr_error lowered]
    | ok expr =>
      exact False.elim (unsupported ⟨⟨expr⟩, .function name (lowerExpr_sound lowered)⟩)

private theorem lower_no_scope_error (source : Source.Module) (diagnostic : Source.Diagnostic) :
    lower source ≠ .error (.scope diagnostic) := by
  intro failed
  unfold lower at failed
  split at failed
  next name value =>
    cases lowered : lowerExpr value with
    | ok expr => simp [Except.map, lowered] at failed
    | error error =>
      simp [Except.map, lowered] at failed
      subst error
      cases lowerExpr_error lowered
  next => simp at failed

theorem rejects_iff (source : Source.Module) (error : Error) :
    compile source = .error error ↔ Rejection source error := by
  cases analyzed : Source.analyze source with
  | error diagnostic =>
    cases error <;> simp [compile, Rejection, analyzed]
  | ok scope =>
    cases error with
    | scope diagnostic => simp [compile, Rejection, analyzed, lower_no_scope_error]
    | moduleShape => simp [compile, Rejection, analyzed, lower_bad_module]
    | expressionShape => simp [compile, Rejection, analyzed, lower_bad_expression]

end Silmaril.Proofs.Languages.Python.Compile.Closed
