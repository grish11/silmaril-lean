module

import Silmaril.Languages.PythonStarlark.ClosedReturn.Thms
import Silmaril.Languages.Python.Core.Thms
meta import Silmaril.Languages.PythonStarlark.ClosedReturn.Defs
meta import Silmaril.Languages.Python.Core.Thms
meta import Silmaril.Languages.Starlark.Denotation.Defs

open Silmaril.Languages Silmaril.Languages.PythonStarlark.ClosedReturn
open Silmaril.Semantics.Operational

private def signed : IntBody :=
  ⟨.binary .add (.binary .floorDiv (.literal (-7)) (.literal 3))
    (.binary .floorDiv (.literal 7) (.literal (-3)))⟩

example : PythonObserves .arithmetic signed.python (.returned (-6)) ∧
    StarlarkObserves signed.starlark (.returned (-6)) :=
  have py : PythonObserves .arithmetic signed.python (.returned (-6)) :=
    (python_observes_iff (int_admitted signed)).mpr rfl
  ⟨py, (agree signed _).mp py⟩

example : ¬ PythonObserves .arithmetic signed.python .diverges :=
  fun observed => starlark_no_divergence signed.starlark ((agree signed _).mp observed)

private def dividesByZero : Expr Int := .binary .floorDiv (.literal 1) (.literal 0)

-- Both operands can reduce. The Python first step leaves the right subtree untouched.
private def leftError : IntBody := ⟨.binary .add dividesByZero (.binary .add (.literal 2) (.literal 5))⟩

example : Python.Core.Step leftError.python.start none (.raising .zeroDivisionError) :=
  .expr (.left (.compute (.divZero 1)))

example : StarlarkObserves leftError.starlark .zeroDivision :=
  .executes (int_resolves leftError)
    (.retError (.binaryLeftError (.binary .int .int (by rfl))))

private def rightError : IntBody := ⟨.binary .add (.literal 9) dividesByZero⟩

example : PythonObserves .arithmetic rightError.python .zeroDivision ∧
    StarlarkObserves rightError.starlark .zeroDivision :=
  have py : PythonObserves .arithmetic rightError.python .zeroDivision :=
    (python_observes_iff (int_admitted rightError)).mpr rfl
  ⟨py, (agree rightError _).mp py⟩

example : PythonObserves .addition leftError.python .rejected :=
  .rejected (Python.Core.noEntry_iff.mpr (by decide))

example : ¬ PythonObserves .addition leftError.python .unsupported := by
  intro observed
  generalize eq : Observation.unsupported = observation at observed
  cases observed with
  | finite may =>
    have denied : ¬ Python.Core.Profile.addition.supports leftError.python.value := by decide
    exact denied (Python.Core.model_may_iff.mp may).1
  | rejected => cases eq
  | unsupported bad => exact Python.Core.model_safe bad
  | diverges => cases eq

example : (Python.Core.semantics .addition).ub leftError.python.start :=
  .inr (by decide)

private def truePlusOne : NumericBody := ⟨.add, .literal (.bool true), .literal (.int 1)⟩

private theorem truePlusOneEval :
    Starlark.Eval {} (truePlusOne.body.value.starlark NumericLiteral.starlarkResolved)
      (.error (.binaryType .add)) :=
  Starlark.Eval.binary (op := .add) (a := .bool true) (b := .int 1)
    (Starlark.Eval.read (ref := .predeclared (.bool true))) (.int (n := 1)) (by rfl)

theorem bool_add_separates :
    PythonObserves .arithmetic truePlusOne.python (.returned 2) ∧
    StarlarkObserves truePlusOne.starlark (.starlarkError (.binaryType .add)) ∧
    ¬ StarlarkObserves truePlusOne.starlark (.returned 2) := by
  have resolves := numeric_resolves truePlusOne
  have fails : Starlark.Exec {} (.ret (some (truePlusOne.body.value.starlark NumericLiteral.starlarkResolved)))
      (.error (.binaryType .add)) :=
    .retError truePlusOneEval
  exact ⟨(python_observes_iff (numeric_admitted truePlusOne)).mpr rfl,
    (starlark_observes_exec resolves fails).mpr rfl,
    fun observed => Observation.noConfusion ((starlark_observes_exec resolves fails).mp observed)⟩

-- Distinct potential errors make evaluation order observable in the Boolean extension.
private def twoErrors (first : Bool) : NumericBody :=
  let zero := Expr.binary .floorDiv (.literal (.int 1)) (.literal (.int 0))
  let typeError := truePlusOne.body.value
  if first then ⟨.add, zero, typeError⟩ else ⟨.add, typeError, zero⟩

example : StarlarkObserves (twoErrors true).starlark .zeroDivision :=
  .executes (numeric_resolves (twoErrors true)) (.retError (.binaryLeftError (.binary .int .int (by rfl))))

example : StarlarkObserves (twoErrors false).starlark (.starlarkError (.binaryType .add)) :=
  .executes (numeric_resolves (twoErrors false)) (.retError (.binaryLeftError truePlusOneEval))

/-- Run both public entry points in addition to checking the relational derivations. -/
public def main : IO Unit := do
  let python := Python.Core.run .arithmetic truePlusOne.python truePlusOne.python.start.budget
  let starlark := Starlark.runFunctionBody [] [] truePlusOne.starlark
  match python, starlark with
  | some (.stop _ (.observed (.returned (.ok value)))), .error (.dynamic (.binaryType .add)) =>
    unless value == 2 do throw (IO.userError "Python Boolean addition gave an unexpected integer")
  | _, _ => throw (IO.userError "Boolean addition did not yield the specified separating outcomes")

#print axioms agree
#print axioms int_resolves
#print axioms starlark_observes_iff
#print axioms starlark_total
#print axioms bool_add_separates
