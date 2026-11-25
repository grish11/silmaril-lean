module

import Silmaril.Languages.Python.Core.Module.Thms
meta import Silmaril.Languages.Python.Core.Module.Defs
meta import Silmaril.Languages.Python.Core.Defs

open Silmaril.Languages.Python.Core.Module

private def initial : Globals :=
  Globals.ofBindings [("seed", .int 5), ("keep", .bool true), ("seed", .int 40)]

private def int (value : Int) : Expr := .literal (.int value)
private def truth (value : Bool) : Expr := .literal (.bool value)
private def add : Expr → Expr → Expr := .binary (.arithmetic .add)
private def divide : Expr → Expr → Expr := .binary (.arithmetic .floorDiv)

private def normalEntry : Entry := ⟨initial, [
  .assignGlobal "x" (add (add (.readGlobal "seed") (truth true)) (int 1)),
  .assignGlobal "flag" (.binary .equal (.readGlobal "x") (int 42)),
  .assert (.readGlobal "flag")]⟩

private def assertionEntry : Entry := ⟨initial, [
  .assignGlobal "x" (int 42),
  .assert (int 0),
  .assignGlobal "x" (int 0),
  .assignGlobal "later" (int 1)]⟩

private def missingEntry : Entry := ⟨initial, [
  .assignGlobal "x" (.readGlobal "seed"),
  .assignGlobal "x" (add (.readGlobal "missing") (divide (int 1) (int 0)))]⟩

private def divisionEntry : Entry := ⟨initial, [.assert (divide (int 1) (int 0))]⟩

private def assertTrace : List Label :=
  [.bindGlobal "x" (.int 42), .complete (.raised .assertionError)]

example : initial.lookup "seed" = some (.int 40) := rfl
example : initial.lookup "x" = none := rfl

example :
    normalEntry.run.1 = [.bindGlobal "x" (.int 42), .bindGlobal "flag" (.bool true), .complete .normal] := rfl

example : labelled.Finishes assertionEntry.start assertTrace
    (.returned ⟨.raised .assertionError, initial.bind "x" (.int 42)⟩) :=
  Entry.finishes_iff.mpr ⟨_, rfl, rfl⟩

example : assertionEntry.run.2 = .finished ⟨.raised .assertionError, initial.bind "x" (.int 42)⟩ := rfl

-- A failed RHS keeps the old target and the first error takes precedence.
example :
    missingEntry.run.2 = .finished ⟨.raised (.nameError "missing"), initial.bind "x" (.int 40)⟩ := rfl
example : divisionEntry.run.2 = .finished ⟨.raised (.arithmetic .zeroDivisionError), initial⟩ := rfl
example : runPrefix 0 assertionEntry.start = ([], assertionEntry.start) := rfl

private def renderCompletion : Completion → String
  | .normal => "normal"
  | .raised .assertionError => "AssertionError"
  | .raised (.nameError name) => "NameError:" ++ name
  | .raised (.arithmetic .zeroDivisionError) => "ZeroDivisionError"

private def renderBinding : Option Value → String
  | none => "absent"
  | some (.int value) => "int:" ++ toString value
  | some (.bool value) => "bool:" ++ toString value

private def report (fixture : String) (entry : Entry) : IO Unit :=
  match entry.run.2 with
  | .running .. => throw (IO.userError s!"{fixture} remained live")
  | .finished observation =>
    let names := ["seed", "keep", "x", "flag", "later"]
    let values := names.map (fun name => renderBinding (observation.globals.lookup name))
    IO.println (String.intercalate "\t"
      ("module-entry" :: fixture :: renderCompletion observation.completion :: values))

public def main : IO Unit := do
  report "normal" normalEntry
  report "assertion" assertionEntry
  report "missing" missingEntry
  report "division" divisionEntry

#print axioms Expr.eval_iff
#print axioms State.advance_iff
#print axioms Step.deterministic
#print axioms model_safe
#print axioms noDiverges
#print axioms run_path
#print axioms Entry.run_finishes
#print axioms Entry.finishes_iff
