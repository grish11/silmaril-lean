module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Async.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Handles.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Async.Transfer

open Silmaril.Wasm.Component Silmaril.Wasm.Component.AsyncRef Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime

inductive Issue where
  | borrowedElement
  | missingEndpoint
  | wrongType
  | stillOwned
  | notIdle
  | inWaitableSet
  deriving DecidableEq, Repr

variable {E : CoreEngine} {World : Type}

/-- REF requires that a transferred element type not contain a borrow. Check it before
touching a table, including a borrow in an inactive branch of the element schema. -/
def schema (element : Element) : Except Issue Unit :=
  if element.any ABI.containsBorrow then .error .borrowedElement else .ok ()

/-- Move a typed readable end out of a guest table using canonical lift. Dynamic traps
still have reference effects; this performs no inspecting lookup ahead of the lift. -/
def take (limits : Component.Limits) (cx : LiftLowerContext E) (channel : Channel)
    (element : Element) (slot : Nat) :
    P E World (Except Issue (Endpoint (channel.endKind .read) element)) :=
  match schema element with
  | .error issue => pure (.error issue)
  | .ok () => do
    let id ← liftAsyncValue limits (channel.endKind .read) cx element slot
    return .ok ⟨id⟩

/-- Check the host-side preconditions that canonical lower assumes. Possessing a Lean
endpoint value is not evidence of current ownership; it may alias an already lowered end. -/
def readyToGive (store : CStore E) (channel : Channel) (element : Element)
    (value : Endpoint (channel.endKind .read) element) : Except Issue Unit := do
  schema element
  match store.end? value.id with
  | none => throw .missingEndpoint
  | some endpoint =>
    if endpoint.kind != channel.endKind .read || endpoint.t != element then throw .wrongType
    if endpoint.owner.isSome || endpoint.index.isSome then throw .stillOwned
    if endpoint.state != .idle then throw .notIdle
    if endpoint.common.wset.isSome then throw .inWaitableSet

/-- Give the same arena object to a guest. Rejection does not change the store. After
preflight passes, canonical lower retains its own order of ownership update and allocation. -/
def give (limits : Component.Limits) (cx : LiftLowerContext E) (channel : Channel)
    (element : Element) (value : Endpoint (channel.endKind .read) element) : P E World (Except Issue Nat) := do
  match readyToGive (← getStore) channel element value with
  | .error issue => return .error issue
  | .ok () => return .ok (← lowerAsyncValue limits (channel.endKind .read) cx value.id)

end Silmaril.Wasm.Game.HandleAccept.Wit.Async.Transfer
