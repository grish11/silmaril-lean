module

public import Silmaril.Languages.PythonStarlark.ClosedReturn.Defs
public import Silmaril.Languages.Python.Core.Thms
public import Silmaril.Languages.Starlark.Thms
public import Silmaril.Proofs.Languages.PythonStarlark.ClosedReturn.Resolution

public section

namespace Silmaril.Proofs.Languages.PythonStarlark.ClosedReturn

open Silmaril.Languages.PythonStarlark.ClosedReturn Silmaril.Languages
open Silmaril.Semantics.Operational

variable {observation : Observation}

theorem python_admitted {Literal : Type} (literal : Literal → Int) (expr : Expr Literal) :
    Python.Core.Profile.arithmetic.supports (expr.python literal) := by
  induction expr with
  | literal => rfl
  | binary op left right leftIH rightIH =>
    change (Python.Core.Profile.arithmetic.allows op.python &&
      Python.Core.Profile.arithmetic.supports (left.python literal) &&
      Python.Core.Profile.arithmetic.supports (right.python literal)) = true
    rw [leftIH, rightIH]
    cases op <;> rfl

theorem python_observes_iff {profile : Python.Core.Profile} {body : Python.Core.Body}
    (admitted : profile.supports body.value) :
    PythonObserves profile body observation ↔ observation = observePython (.returned body.value.eval) := by
  constructor
  · intro seen
    cases seen with
    | finite may => rw [(Python.Core.model_may_iff.mp may).2]
    | rejected missing => exact ((Python.Core.noEntry_iff.mp missing) admitted).elim
    | unsupported bad => exact (Python.Core.model_safe bad).elim
    | diverges _ infinite => exact (Python.Core.noDiverges _ _ infinite).elim
  · rintro rfl
    exact .finite (Python.Core.model_may_iff.mpr ⟨admitted, rfl⟩)

private theorem starlark_run_rejected {body : Starlark.SourceStmt} {error : Starlark.StaticError}
    (rejected : Starlark.resolveFunctionBody [] [] body = .error error) :
    observeStarlark (Starlark.runFunctionBody [] [] body) = .rejected := by
  simp [Starlark.runFunctionBody, rejected, bind, Except.bind, Except.mapError]
  rfl

private theorem starlark_run_resolved {body : Starlark.SourceStmt} {stmt : Starlark.ResolvedStmt}
    (resolved : Starlark.resolveFunctionBody [] [] body = .ok stmt) :
    observeStarlark (Starlark.runFunctionBody [] [] body) =
      observeStarlarkExec (Starlark.denoteStmt stmt {}) := by
  simp only [Starlark.runFunctionBody, List.map_nil, resolved, bind, Except.bind, Except.mapError]
  change observeStarlark (((Starlark.denoteStmt stmt {}).mapError Starlark.Failure.dynamic).bind _) =
    observeStarlarkExec (Starlark.denoteStmt stmt {})
  cases Starlark.denoteStmt stmt {} <;> rfl

theorem starlark_observes_iff {body : Starlark.SourceStmt} :
    StarlarkObserves body observation ↔ observation = observeStarlark (Starlark.runFunctionBody [] [] body) := by
  constructor
  · intro seen
    cases seen with
    | rejected rejected => exact (starlark_run_rejected rejected).symm
    | executes resolved exec =>
      rw [starlark_run_resolved resolved, (Starlark.exec_iff_denoteStmt ..).mp exec]
  · intro seen
    cases resolved : Starlark.resolveFunctionBody [] [] body with
    | error error =>
      rw [starlark_run_rejected resolved] at seen
      exact seen ▸ StarlarkObserves.rejected resolved
    | ok stmt =>
      rw [starlark_run_resolved resolved] at seen
      exact seen ▸ StarlarkObserves.executes resolved ((Starlark.exec_iff_denoteStmt ..).mpr rfl)

theorem starlark_observes_exec {body : Starlark.SourceStmt} {stmt : Starlark.ResolvedStmt}
    {result : Starlark.Result Starlark.Completion}
    (resolved : Starlark.resolveFunctionBody [] [] body = .ok stmt) (exec : Starlark.Exec {} stmt result) :
    StarlarkObserves body observation ↔ observation = observeStarlarkExec result := by
  rw [starlark_observes_iff, starlark_run_resolved resolved, (Starlark.exec_iff_denoteStmt ..).mp exec]

theorem starlark_total {stmt : Starlark.ResolvedStmt} (frame : Starlark.Frame) :
    ∃ result, Starlark.Exec frame stmt result :=
  ⟨_, (Starlark.exec_iff_denoteStmt ..).mpr rfl⟩

private theorem starlark_exec_not_diverges (result : Starlark.Result Starlark.Completion) :
    observeStarlarkExec result ≠ .diverges := by
  cases result with
  | ok result =>
    cases value : result.returned.getD .none <;> simp [observeStarlarkExec, value, observeStarlark]
  | error error =>
    cases error <;> simp [observeStarlarkExec, observeStarlark]
    case zeroDivisor op => cases op <;> simp

theorem starlark_no_divergence (body : Starlark.SourceStmt) : ¬ StarlarkObserves body .diverges := by
  intro seen
  generalize eq : Observation.diverges = observed at seen
  cases seen with
  | rejected => cases eq
  | executes _ exec => exact starlark_exec_not_diverges _ eq.symm

private def liftInt : Python.Core.Completion → Starlark.Result Starlark.Value
  | .ok value => .ok (.int value)
  | .error .zeroDivisionError => .error (.zeroDivisor .floorDiv)

private theorem bin_related (op : Op) (left right : Int) :
    Starlark.applyBinary op.starlark (.int left) (.int right) =
      liftInt (op.python.eval left right) := by
  cases op with
  | add => rfl
  | floorDiv =>
    by_cases zero : right = 0 <;>
      simp [Op.starlark, Op.python, Starlark.applyBinary, Python.Core.BinOp.eval, zero, liftInt]

private theorem eval_related (expr : Expr Int) (frame : Starlark.Frame) :
    Starlark.Eval frame (expr.starlark .int) (liftInt ((expr.python id).eval)) := by
  induction expr with
  | literal n => exact .int
  | binary op left right leftIH rightIH =>
    cases lhs : (left.python id).eval with
    | error error =>
      cases error
      rw [lhs] at leftIH
      simpa [Expr.python, Expr.starlark, Python.Core.Expr.eval, Except.bind, lhs, liftInt] using
        Starlark.Eval.binaryLeftError (op := op.starlark) (right := right.starlark .int) leftIH
    | ok a =>
      rw [lhs] at leftIH
      cases rhs : (right.python id).eval with
      | error error =>
        cases error
        rw [rhs] at rightIH
        simpa [Expr.python, Expr.starlark, Python.Core.Expr.eval, Except.bind, lhs, rhs, liftInt] using
          Starlark.Eval.binaryRightError (op := op.starlark) leftIH rightIH
      | ok b =>
        rw [rhs] at rightIH
        simpa [Expr.python, Expr.starlark, Python.Core.Expr.eval, Except.bind, lhs, rhs, ← bin_related] using
          Starlark.Eval.binary (op := op.starlark) leftIH rightIH (by cases op <;> rfl)

theorem agree (body : IntBody) : Agree body := by
  intro observation
  rw [python_observes_iff (body := body.python) (python_admitted id body.value)]
  have resolved := int_resolves body
  have eval := eval_related body.value {}
  change observation = observePython (.returned (body.value.python id).eval) ↔
    StarlarkObserves body.starlark observation
  cases result : (body.value.python id).eval with
  | ok value =>
    rw [result] at eval
    exact (starlark_observes_exec resolved (.retSome eval)).symm
  | error error =>
    cases error
    rw [result] at eval
    exact (starlark_observes_exec resolved (.retError eval)).symm

end Silmaril.Proofs.Languages.PythonStarlark.ClosedReturn
