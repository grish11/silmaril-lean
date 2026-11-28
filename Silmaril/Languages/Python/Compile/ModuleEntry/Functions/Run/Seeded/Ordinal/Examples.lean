module

import Batteries.Data.Except
import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Thms
meta import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Defs
meta import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Defs
meta import Silmaril.Languages.Python.Core.Module.SeededCall.Observation.Defs
meta import Silmaril.Languages.Python.Core.Closure.Defs
meta import Silmaril.Languages.Python.Source.Scope.Defs

namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded

open Core.Module.SeededCall (Namespace Result)

private def ordinalTest (points : List UInt32) (right : Source.Expr) : Source.Stmt :=
  let call := Source.Expr.callWith (.name "ord") [(.positional, .text points)]
  .assert_ (.comparison call [(.eq, right)]) none

private def checkRun (space : Namespace) (point : UInt32) (right : Source.Expr)
    (completion : Except ModuleFailure Unit) (receipt : Result) : Bool := Id.run do
  let source : Source.Module := ⟨[.assign "keep" (.integer 7), ordinalTest [point] right,
    .assign "tail" (.integer 9)]⟩
  let .ok compiled := Run.compile source | return false
  let heap : Core.Closure.Heap := ⟨1, fun address => if address = 0 then some (.int 23) else none⟩
  let lists : Core.Module.ListHeap := ⟨#[[.int 31]]⟩
  let outcome := run space compiled heap (lists := lists)
  let preserved := space.bindGlobal "keep" (.int 7)
  let expected := if completion.isOk then preserved.bindGlobal "tail" (.int 9) else preserved
  return outcome.completion == completion && outcome.residual.moduleGlobals == expected.moduleGlobals &&
    outcome.residual.builtins == expected.builtins && outcome.heap.next == 1 &&
    (outcome.heap.contents 0).map seededValue == some (.int 23) && outcome.lists == lists &&
    outcome.calls.map (fun call => (call.callee, call.observation.result)) == [("ord", receipt)] &&
    outcome.calls.all (fun call => call.observation.caught.isNone)

private def expressionRejected (points : List UInt32) : Bool :=
  match Run.compile ⟨[ordinalTest points (.integer 0)]⟩ with
  | .error (.source (.scalar .expressionProfile)) => true
  | _ => false

private def stock : Namespace := legacyOrdSeed .builtin

#guard checkRun stock 0xd800 (.integer 55296) (.ok ()) (.ok (.int 55296))
#guard checkRun stock 0x10400 (.integer 66560) (.ok ()) (.ok (.int 66560))
#guard checkRun stock 0x10ffff (.integer 1114111) (.ok ()) (.ok (.int 1114111))
#guard checkRun stock 1 (.boolean true) (.ok ()) (.ok (.int 1))
#guard checkRun stock 97 (.name "missing_right")
  (.error (.raised (.runtime (.nameError "missing_right")))) (.ok (.int 97))
#guard checkRun .empty 97 (.name "missing_right")
  (.error (.raised (.runtime (.nameError "ord")))) (.error (.raised (.runtime (.nameError "ord"))))
#guard checkRun (stock.bindGlobal "ord" .none) 97 (.name "missing_right")
  (.error (.raised (.runtime .notCallable))) (.error (.raised (.runtime .notCallable)))
#guard expressionRejected [0x110000]
#guard expressionRejected [0xd801, 0xdc00]
#guard expressionRejected []

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded
