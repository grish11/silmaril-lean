module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record

open Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower (Authority Object)

structure Access (E : CoreEngine) (World : Type) (sig : Signature) where
  read : P E World (State sig)
  spendOwner : HandleObjId → P E World Unit
  spendEndpoint : EndId → P E World Unit

def Access.direct {E : CoreEngine} {sig : Signature} : Access E (State sig) sig where
  read := hostGet
  spendOwner id := do
    let current ← hostGet
    hostSet { current with held := current.held.filter (fun receipt => receiptId receipt != id) }
  spendEndpoint id := do
    let current ← hostGet
    hostSet { current with endpoints := current.endpoints.filter (· != id) }

def prepareOwner {sig : Signature} (state : State sig) (receipt : Receipt) :
    Except RecordLower.Issue (Nat × State sig) := do
  let (representation, next) ← (state.prepare receipt.1 (receiptId receipt)).mapError .claims
  if representation != receipt.2.representation then throw .ownerReceipt
  return (representation, next)

def prepareEndpoint {E : CoreEngine} {sig : Signature} (store : CStore E) (state : State sig)
    (channel : Async.Channel) (element : Async.Element) (id : EndId) :
    Except RecordLower.Issue (State sig) := do
  let next ← (state.spendEndpoint id).mapError .claims
  (Async.Transfer.readyToGive store channel element ⟨id⟩).mapError
    (RecordLower.Issue.claims ∘ Claims.Issue.endpointTransfer)
  return next

/-- Dry-run each claim in order on a disposable state. An alias fails exactly where a
second occurrence tries to reserve the same arena identity. No live claims are changed. -/
def prepare {E : CoreEngine} {sig : Signature} (store : CStore E) (state : State sig) :
    List Object → Except RecordLower.Issue Unit
  | [] => .ok ()
  | .owner receipt :: rest => do
    let (_, next) ← prepareOwner state receipt
    prepare store next rest
  | .shared (.endpoint channel element id) :: rest => do
    let next ← prepareEndpoint store state channel element id
    prepare store next rest
  | .shared (.errorContext id) :: rest =>
    if (store.errCtx? id).isSome then prepare store state rest else .error (.preflight .missingContext)

/-- The ordered exclusive claims of a mixed lowering plan. Shared error
contexts are observations, not claims to spend. -/
def exclusiveSpends : List Object → List Spend
  | [] => []
  | .owner receipt :: rest => .owner (receiptId receipt) :: exclusiveSpends rest
  | .shared (.endpoint _ _ id) :: rest => .endpoint id :: exclusiveSpends rest
  | .shared (.errorContext _) :: rest => exclusiveSpends rest

def authority {E : CoreEngine} {World : Type} {sig : Signature} (access : Access E World sig)
    (limits : Component.Limits) (cx : LiftLowerContext E) : Authority E World where
  prepare plan := do
    return prepare (← getStore) (← access.read) plan
  transfer index object := do
    let state ← access.read
    match object with
    | .owner receipt =>
      match prepareOwner state receipt with
      | .error issue => return .error (.nested index issue)
      | .ok (representation, _) =>
        return .ok (← commitOwner (access.spendOwner (receiptId receipt)) limits cx receipt.1 representation)
    | .shared (.endpoint channel element id) =>
      match prepareEndpoint (← getStore) state channel element id with
      | .error issue => return .error (.nested index issue)
      | .ok _ =>
        access.spendEndpoint id
        return .ok (← lowerAsyncValue limits (channel.endKind .read) cx id)
    | .shared (.errorContext id) =>
      if ((← getStore).errCtx? id).isNone then
        return .error (.field index (.beforeAllocation .missingContext))
      return .ok (← lowerErrorContext limits cx id)

def preflight {E : CoreEngine} (cx : LiftLowerContext E) (type : TypeOf)
    (payload : Payload type) (output : Stored.Lower.Output) :
    Except RecordLower.Issue (List RecordLower.Field × List Object) := do
  (OwnedMemory.checkSchema type).mapError (RecordLower.Issue.preflight ∘ Endpoints.Lower.Issue.schema)
  RecordLower.compileRecord cx type payload.val.value payload.val.owners output

/-- Lower a mixed record from ordered observations and separate live claims. The
shared emitter rechecks the live claims after allocation and before each transfer.
On a later failure it retains completed writes, transfers and allocator effects. -/
def lower {E : CoreEngine} {World : Type} {sig : Signature} (access : Access E World sig)
    (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E) (type : TypeOf)
    (payload : Payload type) (output : Stored.Lower.Output) :
    P E World (Except RecordLower.Issue output.Result) :=
  RecordLower.Internal.lowerCompiled limits quirks cx (authority access limits cx)
    type payload.val.value output (preflight cx type payload output)

def lowerRoot {E : CoreEngine} {World : Type} {sig : Signature} (access : Access E World sig)
    (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E) (tree : Tree sig)
    (output : Stored.Lower.Output) : P E World (Except RecordLower.Issue output.Result) :=
  match tree with
  | .atom impossible => impossible.elim
  | .tag payload _ _ => lower access limits quirks cx (sig.payload payload.1) payload.2 output

def preflightValue {E : CoreEngine} (cx : LiftLowerContext E) (type : TypeOf)
    (payload : Payload type) (output : Stored.Lower.Output) :
    Except RecordLower.Issue (RecordLower.Field × List Object) := do
  (OwnedMemory.checkSchema type).mapError
    (RecordLower.Issue.preflight ∘ Endpoints.Lower.Issue.schema)
  RecordLower.compileValue cx type payload.val.value payload.val.owners output

/-- Return a checked tree payload at any supported root type, not just a record.
The root memory range is checked before the emitter transfers the first claim. -/
def lowerValue {E : CoreEngine} {World : Type} {sig : Signature} (access : Access E World sig)
    (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E) (type : TypeOf)
    (payload : Payload type) (output : Stored.Lower.Output) : P E World (Except RecordLower.Issue output.Result) :=
  let access := authority access limits cx
  RecordLower.Internal.lowerWithPlan quirks cx access type payload.val.value
    (preflightValue cx type payload output) RecordLower.Field.objects fun width field =>
      RecordLower.Internal.emitValue limits quirks cx access width type field output

def lowerPayloadRoot {E : CoreEngine} {World : Type} {sig : Signature} (access : Access E World sig)
    (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E) (tree : Tree sig)
    (output : Stored.Lower.Output) : P E World (Except RecordLower.Issue output.Result) :=
  match tree with
  | .atom impossible => impossible.elim
  | .tag payload _ _ => lowerValue access limits quirks cx (sig.payload payload.1) payload.2 output

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record
