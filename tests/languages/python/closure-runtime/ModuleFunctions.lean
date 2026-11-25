module

import Silmaril.Languages.Python.Core.Module.Functions.Thms

open Silmaril.Languages.Python.Core.Closure
open Silmaril.Languages.Python.Core.Module.Functions

private def top : TopFunction := ⟨⟨1, ⟨0, 1, 0⟩⟩, rfl⟩

private def definition : Dispatch.Definition Executor.Body top.ref.layout :=
  ⟨⟨[.owned ⟨0, by decide⟩], by decide⟩, .ret (.readGlobal "x")⟩

private def table : Executor.CodeTable :=
  fun key => if key = top.ref.key then some ⟨top.ref.layout, definition⟩ else none

private def initial : Session :=
  (Session.mk Executor.emptyGlobals Heap.empty).bindGlobal "result" (.int 99)

private def invoke (session : Session) (target : Destination) (arguments : List Operand) :
    Option Observation :=
  ((session.prepareCall target (.readGlobal "f") arguments).runPrefix table 16).2.finish?

example : (match invoke initial .discard [] with
    | some ⟨.raised (.nameError "f"), _⟩ => true
    | _ => false) = true := rfl

private def lateBinding : Option Observation := do
  let published ← ((initial.bindGlobal "x" (.int 1)).publish table "f" top).toOption
  let live := published.bindGlobal "x" (.int 42)
  invoke live (.bindGlobal "result") [.literal (.int (-7))]

example : (match lateBinding with
    | some ⟨.returned (.int 42), residual⟩ =>
      residual.globals "x" = some (.int 42) ∧ residual.globals "result" = some (.int 42) ∧
        residual.globals "f" = some top.value ∧ residual.heap.lookup ⟨0⟩ = some (some (.int (-7)))
    | _ => False) := ⟨rfl, rfl, rfl, rfl⟩

private def missingBodyGlobal : Option Observation := do
  let published ← (initial.publish table "f" top).toOption
  invoke published (.bindGlobal "result") [.literal (.int 2)]

example : (match missingBodyGlobal with
    | some ⟨.raised (.nameError "x"), residual⟩ =>
      residual.globals "result" = some (.int 99) ∧ residual.heap.lookup ⟨0⟩ = some (some (.int 2))
    | _ => False) := ⟨rfl, rfl⟩

private def sessionAfterPublish := initial.bindGlobal "f" top.value

example : (match invoke sessionAfterPublish .discard [] with
    | some ⟨.raised (.positionalArity 1 0), _⟩ => true
    | _ => false) = true := rfl

-- Rebinding the function name replaces it in the same namespace.
example : (match invoke (sessionAfterPublish.bindGlobal "f" (.bool true)) .discard [] with
    | some ⟨.raised .notCallable, _⟩ => true
    | _ => false) = true := rfl

-- Argument evaluation precedes the non-callable error.
example : (match invoke (sessionAfterPublish.bindGlobal "f" (.bool true)) .discard [.readGlobal "arg"] with
    | some ⟨.raised (.nameError "arg"), _⟩ => true
    | _ => false) = true := rfl

example : (match invoke (sessionAfterPublish.bindGlobal "x" (.bool false)) .assert [.literal (.int 0)] with
    | some ⟨.assertionError, residual⟩ =>
      residual.globals "x" = some (.bool false) ∧ residual.heap.lookup ⟨0⟩ = some (some (.int 0))
    | _ => False) := ⟨rfl, rfl⟩

example :
    ((sessionAfterPublish.prepareCall .discard (.readGlobal "f") [.literal (.int 0)]).runPrefix table 1).2.finish? =
      none := rfl

example : initial.publish table "f" ⟨⟨2, top.ref.layout⟩, rfl⟩ = .error (.missingCode 2) := rfl

#print axioms Session.publish_iff
#print axioms Executor.stepIn_iff
#print axioms Invocation.run_path
#print axioms Invocation.finish_iff
