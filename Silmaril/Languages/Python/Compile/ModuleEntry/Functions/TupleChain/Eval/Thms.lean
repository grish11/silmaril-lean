module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.TupleChain.Eval.Defs
public import Silmaril.Languages.Python.Core.Module.TupleDispatch.Thms

public section

namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions.TupleChain

open Core.Module.TupleDispatch (Failure Heap)

theorem equal_contents (left right : List Core.Module.TupleDispatch.Element) :
    equal (.contents left) (.contents right) = .ok (Core.Module.TupleDispatch.equalContents left right) := rfl

theorem constructFromName_missing {lookup : Lookup} (heap : Heap) (name : String)
    (missing : lookup.tuple () = none) :
    constructFromName lookup heap name = (.error .missingType, heap) := by
  simp [constructFromName, Core.Module.TupleDispatch.constructWith, missing]

theorem constructFromName_read_failure {lookup : Lookup} (heap : Heap) (name : String)
    {binding : Core.Module.TupleDispatch.TypeBinding} (found : lookup.tuple () = some binding)
    (missing : lookup.global name = none) :
    constructFromName lookup heap name = (.error (.missingName name), heap) := by
  simp [constructFromName, Core.Module.TupleDispatch.constructWith, Lookup.read, found, missing, Except.bind]

theorem constructFromName_stock {lookup : Lookup} (heap : Heap) (name : String)
    (items : List Core.Module.TupleDispatch.Element) (stock : lookup.tuple () = some .stockTuple)
    (read : lookup.global name = some (.contents items)) :
    constructFromName lookup heap name = (.ok (.contents items), heap) := by
  simp [constructFromName, Core.Module.TupleDispatch.constructWith, Lookup.read, stock, read, Except.bind]

theorem scan_error {scope : Source.Scope} (lookup : Lookup)
    (heap reached : Heap) (left : Compared) (operand : TupleOperand scope) (rest : List (TupleOperand scope))
    (error : Failure) (failed : evaluateOperand lookup heap operand = (.error error, reached)) :
    scan lookup heap left (operand :: rest) = ⟨.error error, reached, [.error error]⟩ := by
  simp [scan, failed]

theorem scan_false {scope : Source.Scope} (lookup : Lookup)
    (heap reached : Heap) (left right : Compared) (operand : TupleOperand scope)
    (rest : List (TupleOperand scope))
    (evaluated : evaluateOperand lookup heap operand = (.ok right, reached)) (different : equal left right = .ok false) :
    scan lookup heap left (operand :: rest) = ⟨.ok false, reached, [.ok right]⟩ := by
  simp [scan, evaluated, different]

theorem scan_next {scope : Source.Scope} (lookup : Lookup)
    (heap reached : Heap) (left right : Compared) (operand : TupleOperand scope)
    (rest : List (TupleOperand scope))
    (evaluated : evaluateOperand lookup heap operand = (.ok right, reached)) (same : equal left right = .ok true) :
    scan lookup heap left (operand :: rest) =
      let tail := scan lookup reached right rest
      { tail with reached := .ok right :: tail.reached } := by
  simp [scan, evaluated, same]

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.TupleChain
