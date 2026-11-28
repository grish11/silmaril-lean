module

import Batteries.Data.Except
import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Thms
import Silmaril.Languages.Python.Core.Module.ListObject.Thms
meta import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Defs
meta import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Defs
meta import Silmaril.Languages.Python.Core.Module.Functions.Defs
meta import Silmaril.Languages.Python.Core.Module.SeededCall.Observation.Defs
meta import Silmaril.Languages.Python.Core.Closure.Defs
meta import Silmaril.Languages.Python.Source.Scope.Defs

namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded

open Core.Module.SeededCall (Namespace Result)

private def listTest (reverse : Bool) (expected : List Source.Expr) : Source.Stmt :=
  let call := Source.Expr.callWith (.name "list") [(.positional, .list_ [.boolean true])]
  let literal := Source.Expr.list_ expected
  let (left, right) := if reverse then (literal, call) else (call, literal)
  .assert_ (.comparison left [(.eq, right)]) none

private def checkRun (space : Namespace) (test : Source.Stmt)
    (completion : Except ModuleFailure Unit) (receipt : Result)
    (allocated : Array (List Core.Module.Value)) : Bool := Id.run do
  let source : Source.Module := ⟨[.assign "before" (.integer 7), test, .assign "after" (.integer 9)]⟩
  let .ok compiled := Run.compile source | return false
  let heap : Core.Closure.Heap := ⟨1, fun x => if x = 0 then some (.int 23) else none⟩
  let lists : Core.Module.ListHeap := ⟨#[[.bool true]]⟩
  let result := run space compiled heap (lists := lists)
  let before := space.bindGlobal "before" (.int 7)
  let expected := if completion.isOk then before.bindGlobal "after" (.int 9) else before
  return result.completion == completion && result.residual.moduleGlobals == expected.moduleGlobals &&
    result.residual.builtins == expected.builtins && result.lists.objects == lists.objects ++ allocated &&
    result.heap.next == heap.next && (result.heap.contents 0).map seededValue == some (.int 23) &&
    result.calls.map (fun event => (event.callee, event.observation.result)) == [("list", receipt)] &&
    result.calls.all (fun event => event.observation.caught.isNone)

private def stock : Namespace := legacyListSeed .builtin

#guard checkRun stock (listTest false [.integer 1]) (.ok ()) (.ok (.listObject ⟨2, [.bool true]⟩))
  #[[.bool true], [.bool true], [.int 1]]

#guard checkRun stock (listTest true []) (.error (.raised (.assertionError .empty)))
  (.ok (.listObject ⟨3, [.bool true]⟩)) #[[], [.bool true], [.bool true]]

#guard checkRun .empty (listTest false []) (.error (.raised (.runtime (.nameError "list"))))
  (.error (.raised (.runtime (.nameError "list")))) #[]

#guard checkRun .empty (listTest true []) (.error (.raised (.runtime (.nameError "list"))))
  (.error (.raised (.runtime (.nameError "list")))) #[[]]

#guard checkRun (stock.bindGlobal "list" .none) (listTest false [])
  (.error (.raised (.runtime .notCallable))) (.error (.raised (.runtime .notCallable))) #[[.bool true]]

#guard checkRun (stock.bindGlobal "list" (.builtin .len)) (listTest false [])
  (.error .unsupported) (.error .unsupported) #[[.bool true]]

private def listTruthEvidence (placement : SeedPlacement) : Bool := Id.run do
  let truth value := Source.Stmt.expression (.call (.name "___assertTrue") [value])
  let source : Source.Module := ⟨[truth (.unary .not_ (.list_ [])), truth (.list_ [.integer 42]),
    truth (.list_ []), .assign "unreached" (.integer 9)]⟩
  let .ok compiled := Run.compile source | return false
  let space := legacyTupleIdentitySeed placement
  let result := run space compiled
  let failure : Core.Module.SeededCall.Failure := .raised (.assertionError (.listObject ⟨2, []⟩))
  return result.completion == .error (.ofCall failure) && result.lists.objects == #[[], [.int 42], []] &&
    result.heap.next == 0 && result.residual.moduleGlobals == space.moduleGlobals &&
    result.residual.builtins == space.builtins &&
    result.calls.map (fun item => (item.callee, item.observation.result, item.observation.caught)) ==
      [("___assertTrue", .ok .none, none), ("___assertTrue", .ok .none, none),
        ("___assertTrue", .error failure, none)]

#guard listTruthEvidence .builtin
#guard listTruthEvidence .preamble

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded
