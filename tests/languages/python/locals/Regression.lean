module

import Silmaril.Languages.Python.Core.Locals.Thms
meta import Silmaril.Languages.Python.Core.Locals.Defs
meta import Silmaril.Languages.Python.Core.Locals.Thms
meta import Silmaril.Languages.Python.Core.Context.Defs
meta import Silmaril.Languages.Python.Core.Defs
meta import Silmaril.Semantics.Operational.Determinism.Fuel.Defs

open Silmaril.Languages.Python.Core.Locals
open Silmaril.Semantics.Operational

private def x : Fin 2 := 0
private def y : Fin 2 := 1
private def empty : Store 2 := Store.empty 2

private def sum : Rhs 2 := .arithmetic (.binary .add (.int 2) (.int 5))
private def zero : Rhs 2 := .arithmetic (.binary .floorDiv (.int 1) (.int 0))

private def copyThenOverwrite : Code 2 :=
  .assign x (.arithmetic (.binary .floorDiv (.int 7) (.int (-3))))
    (.assign y (.read x) (.assign x sum (.ret (.read y))))

private def selfReadBeforeWrite : Code 2 := .assign x (.read x) (.ret (.read x))

private def failedReassignment : Code 2 :=
  .assign x (.arithmetic (.int 5))
    (.assign y (.arithmetic (.int 8)) (.assign x zero (.ret (.read y))))

private def localOperands : Code 2 :=
  .assign x (.arithmetic (.int (-3))) (.assign y (.arithmetic (.int 7))
    (.ret (.binary .add (.binary .floorDiv (.read y) (.read x)) (.read y))))

private def readBeforeDivision : Code 2 :=
  .assign x (.binary .add (.read x) zero) (.ret (.read x))

private def divisionBeforeRead : Code 2 :=
  .assign x (.binary .add zero (.read x)) (.ret (.read x))

private def negativeCondition : Code 2 :=
  .assign x (.arithmetic (.int (-9))) (.branch (.read x) (.ret sum) (.ret zero))

private def zeroCondition : Code 2 :=
  .assign x (.arithmetic (.int 0)) (.branch (.read x) (.ret zero) (.ret (.arithmetic (.int 8))))

private def failingCondition : Code 2 :=
  .assign x (.arithmetic (.int 1))
    (.branch (.binary .floorDiv (.read x) (.arithmetic (.int 0)))
      (.ret sum) (.ret (.arithmetic (.int 8))))

private def falseAnd : Code 2 :=
  .assign x (.arithmetic (.int 0)) (.ret (.logical .and (.read x) zero))

private def trueOr : Code 2 :=
  .assign x (.arithmetic (.int (-4))) (.ret (.logical .or (.read x) zero))

private def trueAnd : Code 2 :=
  .assign x (.arithmetic (.int 7)) (.ret (.logical .and (.read x) zero))

private def falseOr : Code 2 :=
  .assign x (.arithmetic (.int 0))
    (.ret (.logical .or (.read x) (.arithmetic (.binary .floorDiv (.int 7) (.int (-3))))))

private def simple : Code 2 := .assign x sum (.ret (.read x))

example : (labelled 2).Finishes (State.enter empty simple) [.write x 7, .exit (.ok 7)]
    (.returned (.ok 7)) :=
  ⟨.finished (empty.write x 7) (.ok 7),
    .silent (.expression (.arithmetic (.compute (.add 2 5)))) <|
      .visible (.assign empty x 7 (.ret (.read x))) <|
        .silent (.expression (.load x 7 rfl)) <|
          .visible (.ret (empty.write x 7) 7) (.nil _),
    .finished _ _⟩

example : run simple 0 = .exhausted (State.enter empty simple) := rfl

example : Step (State.enter empty selfReadBeforeWrite) none (.raising empty (.unboundLocal x)) :=
  .expression (.unbound x rfl)

-- A failing right-hand side preserves the old binding and the unrelated slot.
example :
    (match run failedReassignment failedReassignment.budget with
     | .stop (.finished store (.error (.arithmetic .zeroDivisionError))) _ =>
       store x = some 5 ∧ store y = some 8
     | _ => False) :=
  ⟨rfl, rfl⟩

example : State.advance (State.enter empty readBeforeDivision) =
    some (none, .raising empty (.unboundLocal x)) := rfl

example : State.advance (State.enter empty divisionBeforeRead) =
    some (none, .raising empty (.arithmetic .zeroDivisionError)) := rfl

example : (model 2).May localOperands (.returned (.ok 4)) :=
  model_may_iff.mpr rfl

example : (model 2).May copyThenOverwrite (.returned (.ok (-3))) :=
  model_may_iff.mpr rfl

example : (model 2).May negativeCondition (.returned (.ok 7)) := model_may_iff.mpr rfl

example : (model 2).May zeroCondition (.returned (.ok 8)) := model_may_iff.mpr rfl

example : (model 2).May failingCondition (.returned (.error (.arithmetic .zeroDivisionError))) :=
  model_may_iff.mpr rfl

example : (model 2).May falseAnd (.returned (.ok 0)) := model_may_iff.mpr rfl
example : (model 2).May trueOr (.returned (.ok (-4))) := model_may_iff.mpr rfl
example : (model 2).May falseOr (.returned (.ok (-3))) := model_may_iff.mpr rfl

example : (model 2).May trueAnd (.returned (.error (.arithmetic .zeroDivisionError))) :=
  model_may_iff.mpr rfl

private def outcome (code : Code 2) : IO String :=
  match run code code.budget with
  | .stop _ (.observed (.returned (.ok value))) => pure (toString value)
  | .stop _ (.observed (.returned (.error (.unboundLocal _)))) => pure "UnboundLocalError"
  | .stop _ (.observed (.returned (.error (.arithmetic .zeroDivisionError)))) => pure "ZeroDivisionError"
  | _ => throw (IO.userError "The certified budget should produce a language outcome")

public def main : IO Unit := do
  for (name, code) in [("copy_then_overwrite", copyThenOverwrite),
      ("self_read_before_write", selfReadBeforeWrite), ("failed_reassignment", failedReassignment),
      ("local_operands", localOperands), ("read_before_division", readBeforeDivision),
      ("division_before_read", divisionBeforeRead), ("negative_condition", negativeCondition),
      ("zero_condition", zeroCondition), ("failing_condition", failingCondition),
      ("false_and", falseAnd), ("true_or", trueOr), ("true_and", trueAnd), ("false_or", falseOr)] do
    IO.println s!"parity\t{name}\t{← outcome code}"

#print axioms Rhs.reduce_iff
#print axioms State.advance_iff
#print axioms Step.answer_eq
#print axioms Step.decreases
#print axioms noDiverges
#print axioms model_may_iff
#print axioms closed_may_iff
#print axioms run_sound
#print axioms run_exact
