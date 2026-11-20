module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Async.Transfer.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints

open Silmaril.Formats Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Value
open Silmaril.Wasm.Game.HandleAccept.Wit.Async (Channel Element Endpoint Channel.endKind)

mutual
/-- The endpoint identities moved by a lifted value, in payload order. Sum values only
contain their selected arm; memory and flat lifting validates the complete schema first. -/
def endpointIds : Val → List EndId
  | .future id | .stream id => [id]
  | .list entries | .record entries => endpointIdsIn entries
  | .variant _ value => endpointIdsInOption value
  | _ => []
termination_by structural value => value

def endpointIdsIn : List Val → List EndId
  | [] => []
  | value :: rest => endpointIds value ++ endpointIdsIn rest
termination_by structural values => values

def endpointIdsInOption : Option Val → List EndId
  | none => []
  | some value => endpointIds value
termination_by structural value => value
end

/-- Only a freshly lifted root creates claims. Passing an already-built child is not
another transfer of that child's payload. -/
def rootIds {sig : Signature} : Tree sig → List EndId
  | .atom impossible => impossible.elim
  | .tag label _ _ => endpointIds label.2.val

/-- An observation is durable, but its endpoint may already have been given away.
Use this state with the host operations below; do not promote observations to claims. -/
structure State (sig : Signature) where
  accepted : List (Tree sig) := []
  held : List EndId := []

inductive Issue where
  | lift (issue : Stored.Issue)
  | give (issue : Async.Transfer.Issue)
  | alias
  | unclaimed
  deriving DecidableEq, Repr

/-- Register the endpoints moved into a freshly lifted root. No duplicates are admitted. -/
def State.register {sig : Signature} (state : State sig) (tree : Tree sig) : Except Issue (State sig) :=
  let ids := rootIds tree
  if ids.Nodup ∧ !(ids.any fun id => state.held.contains id) then
    .ok ⟨tree :: state.accepted, ids ++ state.held⟩
  else .error .alias

/-- Prepare to spend one claim. This does not edit the machine's host state yet. -/
def State.spend {sig : Signature} (state : State sig) (id : EndId) : Except Issue (State sig) :=
  if id ∈ state.held then .ok { state with held := state.held.filter (· != id) }
  else .error .unclaimed

variable {E : CoreEngine}

/-- Lift and accept a root in the reference component machine. A lift trap retains the
reference effects, but does not publish a tree or any of the incomplete lift's claims. -/
def acceptNode (sig : Signature) (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (tag : sig.Tag) (input : Input) (children : List (Tree sig)) :
    P E (State sig) (Except Issue (Tree sig)) := do
  match ← buildNode sig limits quirks cx tag input children with
  | .error issue => return .error (.lift issue)
  | .ok tree =>
    match (← hostGet).register tree with
    | .error issue => return .error issue
    | .ok updated =>
      hostSet updated
      return .ok tree

/-- Give one claimed readable endpoint to a guest. Typed refusal does not spend the
claim. Once validated, spend it before canonical lower changes the owner, since
reference table insertion can trap after that change. -/
def give {sig : Signature} (limits : Component.Limits) (cx : LiftLowerContext E) (channel : Channel)
    (element : Element) (endpoint : Endpoint (channel.endKind .read) element) :
    P E (State sig) (Except Issue Nat) := do
  match (← hostGet).spend endpoint.id with
  | .error issue => return .error issue
  | .ok updated =>
    match Async.Transfer.readyToGive (← getStore) channel element endpoint with
    | .error issue => return .error (.give issue)
    | .ok () =>
      hostSet updated
      return .ok (← lowerAsyncValue limits (channel.endKind .read) cx endpoint.id)

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints
