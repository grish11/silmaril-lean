module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Lower.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Lower

open Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Value
open Silmaril.Wasm.Game.HandleAccept.Wit.Async (Channel Element)

inductive Issue where
  | schema (issue : Stored.Issue)
  | abi (issue : Stored.Lower.Issue)
  | indirectPayload
  | decodedType
  | unclaimed
  | endpoint (issue : Async.Transfer.Issue)
  | missingContext
  deriving DecidableEq, Repr

inductive Object where
  | endpoint (channel : Channel) (element : Element) (id : EndId)
  | errorContext (id : ErrCtxId)

abbrev Plan := Except Issue (List Object)

mutual
/-- Inspect active payload objects in canonical order, with their expected element types.
The entire schema is checked separately before this traversal. -/
def objects : TypeOf → Val → Plan
  | .future element, .future id => .ok [.endpoint .future element id]
  | .stream element, .stream id => .ok [.endpoint .stream element id]
  | .errorContext, .errorContext id => .ok [.errorContext id]
  | .fixedList type _, .list values => do
    let parts ← values.mapM (objects type)
    return parts.flatten
  | .record fields, .record values => fieldObjects fields values
  | .tuple types, .record values => tupleObjects types values
  | .variant cases, .variant index value => caseObjects cases index value
  | .option _, .variant 0 none => .ok []
  | .option type, .variant 1 (some value) => objects type value
  | .result ok _, .variant 0 value => optionalObjects ok value
  | .result _ err, .variant 1 value => optionalObjects err value
  | .prim .string, _ | .list _, _ | .map _ _, _ => .error .indirectPayload
  | .prim _, _ | .enum _, .variant _ none | .flags _, .flags _ => .ok []
  | _, _ => .error .decodedType
termination_by structural type => type

def fieldObjects : List (String × TypeOf) → List Val → Plan
  | [], [] => .ok []
  | (_, type) :: fields, value :: values => do
    return (← objects type value) ++ (← fieldObjects fields values)
  | _, _ => .error .decodedType
termination_by structural fields => fields

def tupleObjects : List TypeOf → List Val → Plan
  | [], [] => .ok []
  | type :: types, value :: values => do
    return (← objects type value) ++ (← tupleObjects types values)
  | _, _ => .error .decodedType
termination_by structural types => types

def caseObjects : List (String × Option TypeOf) → Nat → Option Val → Plan
  | [], _, _ => .error .decodedType
  | (_, type) :: _, 0, value => optionalObjects type value
  | _ :: rest, index + 1, value => caseObjects rest index value
termination_by structural cases => cases

def optionalObjects : Option TypeOf → Option Val → Plan
  | none, none => .ok []
  | some type, some value => objects type value
  | _, _ => .error .decodedType
termination_by structural type => type
end

/-- Validate all objects and spend claims only in the proposed next state. A repeated
endpoint fails here, before any guest slots or memory are written. -/
def prepare {E : CoreEngine} {sig : Signature} (store : CStore E) (state : State sig) :
    List Object → Except Issue (State sig)
  | [] => .ok state
  | .endpoint channel element id :: rest => do
    let next ← (state.spend id).mapError (fun _ => .unclaimed)
    (Async.Transfer.readyToGive store channel element ⟨id⟩).mapError .endpoint
    prepare store next rest
  | .errorContext id :: rest =>
    if (store.errCtx? id).isSome then prepare store state rest else .error .missingContext

/-- Reject any schema that can invoke guest allocation, including in a dormant arm.
The direct path does not establish a frame across guest realloc calls. -/
def preflight {E : CoreEngine} (cx : LiftLowerContext E) (type : TypeOf)
    (payload : Payload type) (output : Stored.Lower.Output) : Plan := do
  (Stored.checkSchema type).mapError .schema
  if Validation.containsPtr type then throw .indirectPayload
  (Stored.Lower.checkOptions cx type output).mapError .abi
  objects type payload.val

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Lower
