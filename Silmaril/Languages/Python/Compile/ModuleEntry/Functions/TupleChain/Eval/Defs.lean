module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.TupleChain.Defs
public import Silmaril.Languages.Python.Core.Module.TupleDispatch.Defs
public import Silmaril.Languages.Python.Core.Closure.Defs

@[expose] public section

namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions.TupleChain

open Source (Scope)
open Core.Module.TupleDispatch (Failure Heap Object Result TypeBinding)

def tupleResult : Result → Except Failure Object
  | .tuple object => .ok object
  | .bool _ | .notImplemented => .error .unsupported

def evaluateOperand {scope : Scope} (lookup : Unit → Option TypeBinding) (heap : Heap) :
    TupleOperand scope → Except Failure Object × Heap
  | .literal contents =>
    let (object, reached) := heap.materialize contents
    (.ok object, reached)
  | .add receiver argument | .boundAdd receiver argument =>
    let (result, reached) := Core.Module.TupleDispatch.callBound heap .add receiver (.tuple argument)
    (result.bind tupleResult, reached)
  | .unboundAdd _ receiver argument =>
    let (result, reached) := Core.Module.TupleDispatch.callUnbound heap (lookup ()) .add
      (.tuple receiver) (.tuple argument)
    (result.bind tupleResult, reached)

  | .construct _ argument =>
    Core.Module.TupleDispatch.construct heap (lookup ()) (argument.map fun contents current =>
      let (object, reached) := current.materialize contents
      (.ok object, reached))

structure Observation where
  result : Except Failure Bool
  heap : Heap
  reached : List (Except Failure Object)
  deriving Repr

def equal (left right : Object) : Bool :=
  ClosedSequence.equal ⟨.tuple, left.contents⟩ ⟨.tuple, right.contents⟩

/-- Retain the reached right object as the next left object. The rest is
evaluated only after a successful and true comparison. -/
def scan {scope : Scope} (lookup : Unit → Option TypeBinding) (heap : Heap) (left : Object) :
    List (TupleOperand scope) → Observation
  | [] => ⟨.ok true, heap, []⟩
  | operand :: rest =>
    let (result, reached) := evaluateOperand lookup heap operand
    match result with
    | .error error => ⟨.error error, reached, [result]⟩
    | .ok right =>
      if equal left right then
        let tail := scan lookup reached right rest
        { tail with reached := result :: tail.reached }
      else ⟨.ok false, reached, [result]⟩

/-- Internal tuple addresses are scoped to this comparison and never escape
into the caller namespace or closure heap. -/
def evaluate {scope : Scope} (lookup : Unit → Option TypeBinding) (test : TupleChainTest scope) :
    Observation :=
  let (result, reached) := evaluateOperand lookup .empty test.first
  match result with
  | .error error => ⟨.error error, reached, [result]⟩
  | .ok left =>
    let tail := scan lookup reached left test.links
    { tail with reached := result :: tail.reached }

def runtimeError? : Failure → Option Core.Closure.RuntimeError
  | .missingType => some (.nameError "tuple")
  | .notCallable => some .notCallable
  | .missingAttribute _ | .wrongReceiver _ | .wrongArgument | .unsupported => none

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.TupleChain
