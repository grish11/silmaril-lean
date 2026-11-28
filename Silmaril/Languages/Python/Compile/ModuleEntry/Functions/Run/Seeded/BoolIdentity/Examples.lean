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

private def checkRun (space : Namespace) (argument : Option Source.Expr) (right : Source.Expr)
    (completion : Except ModuleFailure Unit) (receipt : Result) : Bool := Id.run do
  let call := Source.Expr.callWith (.name "bool") (argument.toList.map (.positional, ·))
  let assertion := Source.Stmt.assert_ (.comparison call [(.is_, right)]) none
  let source : Source.Module := ⟨[.assign "keep" (.integer 7), assertion, .assign "tail" (.integer 9)]⟩
  let .ok compiled := Run.compile source | return false
  let heap : Core.Closure.Heap := ⟨1, fun address => if address = 0 then some (.int 23) else none⟩
  let lists : Core.Module.ListHeap := ⟨#[[.int 31]]⟩
  let result := run space compiled heap (lists := lists)
  let preserved := space.bindGlobal "keep" (.int 7)
  let expected := if completion.isOk then preserved.bindGlobal "tail" (.int 9) else preserved
  return result.completion == completion && result.residual.moduleGlobals == expected.moduleGlobals &&
    result.residual.builtins == expected.builtins && result.heap.next == 1 &&
    (result.heap.contents 0).map seededValue == some (.int 23) && result.lists == lists &&
    result.calls.map (fun call => (call.callee, call.observation.result)) == [("bool", receipt)] &&
    result.calls.all (fun call => call.observation.caught.isNone)

private def stock : Namespace := legacyBoolIsinstanceSeed .builtin
private def rightError : Source.Expr := .comparison (.name "missing_right") [(.eq, .integer 0)]

#guard checkRun stock none (.boolean false) (.ok ()) (.ok (.bool false))
#guard checkRun stock (some (.integer (-7))) (.boolean true) (.ok ()) (.ok (.bool true))
#guard checkRun .empty (some (.name "missing_arg")) rightError
  (.error (.raised (.runtime (.nameError "bool")))) (.error (.raised (.runtime (.nameError "bool"))))
#guard checkRun (stock.bindGlobal "bool" .none) (some (.name "missing_arg")) rightError
  (.error (.raised (.runtime (.nameError "missing_arg")))) (.error (.raised (.runtime (.nameError "missing_arg"))))
#guard checkRun (stock.bindGlobal "bool" .none) (some (.integer 0)) rightError
  (.error (.raised (.runtime .notCallable))) (.error (.raised (.runtime .notCallable)))
#guard checkRun (stock.bindGlobal "bool" (.returnedTuple [.int 1])) (some (.integer 0)) rightError
  (.error (.raised (.runtime .notCallable))) (.error (.raised (.runtime .notCallable)))
#guard checkRun stock (some .none_) rightError
  (.error (.raised (.runtime (.nameError "missing_right")))) (.ok (.bool false))
#guard checkRun stock (some (.boolean false)) .none_ (.error (.raised (.assertionError .empty))) (.ok (.bool false))

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded
