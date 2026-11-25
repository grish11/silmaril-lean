module

import Silmaril.Languages.Python.Core.Locals.Finite.Thms
meta import Silmaril.Languages.Python.Core.Locals.Finite.Defs
meta import Silmaril.Languages.Python.Core.Locals.Defs
meta import Silmaril.Languages.Python.Core.Defs
meta import Silmaril.Semantics.Operational.Environment.Finite.Defs
meta import Mathlib.Data.List.AList

/-! # Projecting typed Python local-slot executions -/

open Silmaril.Languages.Python.Core.Locals Silmaril.Languages.Python.Core.Locals.Finite
open Silmaril.Semantics.Operational

private def slot : Fin 2 := 1
private def empty : Store 2 := Store.empty 2
private def readCode : Code 2 := .ret (.read slot)
private def writeThenRead : Code 2 := .assign slot (.arithmetic (.int 17)) readCode
private def initial : Presentation 2 := Presentation.enter ∅ writeThenRead
private def written : Store 2 := empty.write slot 17
private def afterWrite : State 2 := State.enter written readCode
private def afterRead : State 2 := .evaluating written (.arithmetic (.int 17)) .ret
private def success : State 2 := .finished written (.ok 17)

example : (model 2).initial writeThenRead initial.view := entry writeThenRead

example : ∃ next, initial.advance = some (some (.write slot 17), next) ∧ next.view = afterWrite :=
  step_iff.mp (.assign empty slot 17 readCode)

#guard match initial.advance with
  | some (some (.write key value), .evaluating rows (.read readKey) .ret) =>
    key == slot && value == 17 && readKey == slot && rows.lookup slot == some 17 && rows.lookup 0 == none
  | _ => false

private theorem runSome :
    (semantic 2).Execution initial.view [some (.write slot 17), none, some (.exit (.ok 17))]
      success [initial.view, afterWrite, afterRead, success] :=
  .stepL (.assign empty slot 17 readCode)
    (.stepL (.expression (.load slot 17 rfl)) (.stepL (.ret written 17) (.refl _)))

example : ∃ final witnesses,
    (presented 2).Execution initial [some (.write slot 17), none, some (.exit (.ok 17))] final witnesses ∧
      witnesses.map Presentation.view = [initial.view, afterWrite, afterRead, success] ∧
      final.view = success :=
  execution_readback runSome

private def unbound : Error 2 := .unboundLocal slot
private def reading : Presentation 2 := Presentation.enter ∅ readCode
private def raisingState : State 2 := .raising empty unbound
private def failure : State 2 := .finished empty (.error unbound)

private theorem runNone :
    (semantic 2).Execution reading.view [none, some (.exit (.error unbound))]
      failure [reading.view, raisingState, failure] :=
  .stepL (.expression (.unbound slot rfl)) (.stepL (.raise empty unbound) (.refl _))

example : ∃ final witnesses,
    (presented 2).Execution reading [none, some (.exit (.error unbound))] final witnesses ∧
      witnesses.map Presentation.view = [reading.view, raisingState, failure] ∧
      final.completion? = some (.error unbound) := by
  obtain ⟨final, witnesses, trace, views, equal⟩ := execution_readback runNone
  have observes : Observes final.view (.returned (.error unbound)) := by
    rw [equal]
    exact .finished empty _
  obtain ⟨result, returned, same⟩ := terminal_iff.mp observes
  cases same
  exact ⟨final, witnesses, trace, views, returned⟩

example : (Presentation.raising (∅ : Rows 2) unbound).completion? = none := rfl

private def populated : Rows 2 := (∅ : Rows 2).insert slot 17
private def yes : Code 2 := .ret (.arithmetic (.int 2))
private def no : Code 2 := .ret (.arithmetic (.int 3))

example : (Presentation.enter populated (.branch (.arithmetic (.int (-7))) yes no)).advance =
    some (none, Presentation.enter populated yes) := rfl

example : (Presentation.enter populated (.branch (.arithmetic (.int 0)) yes no)).advance =
    some (none, Presentation.enter populated no) := rfl

example : (Presentation.enter populated (.branch (.read 0) yes no)).advance =
    some (none, .raising populated (.unboundLocal 0)) := rfl

private def shortTest : Rhs 2 := .logical .and (.arithmetic (.int 0)) (.read 0)
private def branchEntry := Presentation.enter populated (.branch shortTest yes no)
private def branchTest := (Presentation.enter populated (.branch (.arithmetic (.int 0)) yes no)).view
private def branchNo := (Presentation.enter populated no).view
private def branchExit : State 2 := .finished (Environment.Finite.view populated) (.ok 3)

private theorem runBranch :
    (semantic 2).Execution branchEntry.view [none, none, some (.exit (.ok 3))] branchExit
      [branchEntry.view, branchTest, branchNo, branchExit] :=
  .stepL (.expression (.logicalShort rfl))
    (.stepL (.takeNo _ yes no) (.stepL (.ret _ 3) (.refl _)))

example : ∃ final witnesses,
    (presented 2).Execution branchEntry [none, none, some (.exit (.ok 3))] final witnesses ∧
      witnesses.map Presentation.view = [branchEntry.view, branchTest, branchNo, branchExit] ∧
      final.view = branchExit :=
  execution_readback runBranch
