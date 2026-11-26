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

/-- Literal method traces keep their local objects. Module reads expose
contents for equality and never synthesize an address. -/
inductive Compared where
  | object (value : Object)
  | contents (value : List Core.Module.TupleDispatch.Element)
  | scalar (value : Core.Module.Value)
  | outsideProfile
  deriving DecidableEq, Repr

def Compared.tupleContents? : Compared → Option (List Core.Module.TupleDispatch.Element)
  | .object value => some value.contents
  | .contents value => some value
  | .scalar _ | .outsideProfile => none

def Compared.ofClosure : Core.Closure.Value → Compared
  | .tuple items => .contents items
  | .tupleObject descriptor => .contents descriptor.contents
  | value => (value.scalar?.map .scalar).getD .outsideProfile

structure Lookup where
  tuple : Unit → Option TypeBinding
  global : String → Option Compared := fun _ => none

def Lookup.read (lookup : Lookup) (name : String) : Except Failure Compared :=
  (lookup.global name).elim (.error (.missingName name)) .ok

def constructFromName (lookup : Lookup) (heap : Heap) (name : String) : Except Failure Compared × Heap :=
  Core.Module.TupleDispatch.constructWith heap (lookup.tuple ()) (fun reached => (lookup.read name, reached))
    (fun value => match value with
      | .object _ | .contents _ => .ok value
      | .scalar _ => .error .notIterable
      | .outsideProfile => .error .unsupported)

def evaluateOperand {scope : Scope} (lookup : Lookup) (heap : Heap) :
    TupleOperand scope → Except Failure Compared × Heap
  | .literal contents =>
    let (object, reached) := heap.materialize contents
    (.ok (.object object), reached)
  | .global name _ => (lookup.read name, heap)
  | .add receiver argument | .boundAdd receiver argument =>
    let (result, reached) := Core.Module.TupleDispatch.callBound heap .add receiver (.tuple argument)
    ((result.bind tupleResult).map .object, reached)
  | .unboundAdd _ receiver argument =>
    let (result, reached) := Core.Module.TupleDispatch.callUnbound heap (lookup.tuple ()) .add
      (.tuple receiver) (.tuple argument)
    ((result.bind tupleResult).map .object, reached)
  | .construct _ argument =>
    let (result, reached) := Core.Module.TupleDispatch.construct heap (lookup.tuple ()) (argument.map fun contents current =>
      let (object, reached) := current.materialize contents
      (.ok object, reached))
    (result.map .object, reached)
  | .constructGlobal _ name _ => constructFromName lookup heap name

structure Observation where
  result : Except Failure Bool
  heap : Heap
  reached : List (Except Failure Compared)
  deriving Repr

def equal (left right : Compared) : Except Failure Bool :=
  match left.tupleContents?, right.tupleContents? with
  | some first, some second => .ok (Core.Module.TupleDispatch.equalContents first second)
  | _, _ =>
    match left, right with
    | .outsideProfile, _ | _, .outsideProfile => .error .unsupported
    | .scalar first, .scalar second => .ok (first.equal second)
    | _, _ => .ok false

/-- Retain the reached right object as the next left object. The rest is
evaluated only after a successful and true comparison. -/
def scan {scope : Scope} (lookup : Lookup) (heap : Heap) (left : Compared) :
    List (TupleOperand scope) → Observation
  | [] => ⟨.ok true, heap, []⟩
  | operand :: rest =>
    let (result, reached) := evaluateOperand lookup heap operand
    match result with
    | .error error => ⟨.error error, reached, [result]⟩
    | .ok right =>
      match equal left right with
      | .ok true =>
        let tail := scan lookup reached right rest
        { tail with reached := result :: tail.reached }
      | result => ⟨result, reached, [.ok right]⟩

/-- Internal tuple addresses are scoped to this comparison and never escape
into the caller namespace or closure heap. -/
def evaluate {scope : Scope} (lookup : Lookup) (test : TupleChainTest scope) :
    Observation :=
  let (result, reached) := evaluateOperand lookup .empty test.first
  match result with
  | .error error => ⟨.error error, reached, [result]⟩
  | .ok left =>
    let tail := scan lookup reached left test.links
    { tail with reached := result :: tail.reached }

def runtimeError? : Failure → Option Core.Closure.RuntimeError
  | .missingType => some (.nameError "tuple")
  | .missingName name => some (.nameError name)
  | .notIterable => some .tupleArgumentNotIterable
  | .notCallable => some .notCallable
  | .missingAttribute _ | .wrongReceiver _ | .wrongArgument | .unsupported => none

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.TupleChain
