module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims

open Silmaril.Formats Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.Game.HandleAccept.Wit.Async (Channel Element Endpoint Channel.endKind)

/-- Accepted trees are durable observations. Owners and readable endpoints have separate
one-shot claims. An existing child is not lifted or claimed again. -/
structure State (sig : Signature) where
  accepted : List (Tree sig) := []
  held : List Receipt := []
  endpoints : List EndId := []

inductive Issue where
  | lift (issue : OwnedMemory.Issue)
  | alias
  | unclaimed
  | unclaimedEndpoint
  | endpointTransfer (issue : Async.Transfer.Issue)
  | wrongResourceType
  deriving DecidableEq, Repr

def rootReceipts {sig : Signature} : Tree sig → List Receipt
  | .atom impossible => impossible.elim
  | .tag payload _ _ => payload.2.val.owners

def rootEndpoints {sig : Signature} : Tree sig → List EndId
  | .atom impossible => impossible.elim
  | .tag payload _ _ => Endpoints.endpointIds payload.2.val.value

def receiptId (receipt : Receipt) : HandleObjId := receipt.2.identity

def State.retiredOwner {sig : Signature} (state : State sig) (id : HandleObjId) : Prop :=
  id ∈ (state.accepted.flatMap rootReceipts).map receiptId ∧ id ∉ state.held.map receiptId

/-- Spending is an identity-specific update, not replacement by a previously read state. -/
inductive Spend where
  | owner (id : HandleObjId)
  | endpoint (id : EndId)

def Spend.apply {sig : Signature} (spend : Spend) (state : State sig) : State sig :=
  match spend with
  | .owner id => { state with held := state.held.filter (fun entry => receiptId entry != id) }
  | .endpoint id => { state with endpoints := state.endpoints.filter (· != id) }

def Spend.Live {sig : Signature} (update : Spend) (state : State sig) : Prop :=
  match update with
  | .owner id => id ∈ state.held.map receiptId
  | .endpoint id => id ∈ state.endpoints

/-- Validate all the root's claims together before publishing either class of claim or the
tree. Endpoints can come back through a new legitimate lift; a past observation is not a claim. -/
def State.register {sig : Signature} (state : State sig) (tree : Tree sig) : Except Issue (State sig) :=
  let receipts := rootReceipts tree
  let owners := receipts.map receiptId
  let known := (state.accepted.flatMap rootReceipts ++ state.held).map receiptId
  let endpoints := rootEndpoints tree
  if owners.Nodup ∧ !(owners.any known.contains) ∧
      endpoints.Nodup ∧ !(endpoints.any state.endpoints.contains) then
    .ok ⟨tree :: state.accepted, receipts ++ state.held, endpoints ++ state.endpoints⟩
  else .error .alias

/-- Registration reads only conflicts with the new root's claims. The journals,
unrelated claims, and representations need not agree. Handle selection separately
reads the number of accepted roots. -/
structure State.RegistrationChecksAgree {sig : Signature} (left right : State sig) (tree : Tree sig) : Prop where
  owners : ∀ id ∈ (rootReceipts tree).map receiptId,
    (id ∈ ((left.accepted.flatMap rootReceipts ++ left.held).map receiptId) ↔
      id ∈ ((right.accepted.flatMap rootReceipts ++ right.held).map receiptId))
  endpoints : ∀ id ∈ rootEndpoints tree, (id ∈ left.endpoints ↔ id ∈ right.endpoints)

/-- A spend frames the next root's conflict probes if it cannot remove any
requested conflict. An accepted owner remains a conflict after its spend. -/
def Spend.FramesRegistration {sig : Signature} (update : Spend) (state : State sig) (tree : Tree sig) : Prop :=
  match update with
  | .owner id => id ∉ (rootReceipts tree).map receiptId ∨ id ∈ (state.accepted.flatMap rootReceipts).map receiptId
  | .endpoint id => id ∉ rootEndpoints tree

/-- The ordered acceptance history fixes handle lookup and the next registration
index. Live claims are compared by nominal identity, not by list representation.
This does not compare owner representations used by `State.prepare`. -/
structure State.IndexedClaimsAgree {sig : Signature} (left right : State sig) : Prop where
  accepted : left.accepted = right.accepted
  held : ∀ id, (id ∈ left.held.map receiptId ↔ id ∈ right.held.map receiptId)
  endpoints : ∀ id, (id ∈ left.endpoints ↔ id ∈ right.endpoints)

/-- The held-owner information consulted by `prepare`, indexed by arena
identity. Even on states with duplicate entries the first match matters. -/
def State.ownerObservation {sig : Signature} (state : State sig) (id : HandleObjId) : Option (RtId × Nat) :=
  (state.held.find? (fun receipt => receiptId receipt == id)).map (fun receipt =>
    (receipt.1, receipt.2.representation))

/-- Live equality at one nominal claim. A different owner or endpoint may have
been consumed, and the two acceptance histories need not agree. -/
def Spend.ObservationAgrees {sig : Signature} (probe : Spend) (left right : State sig) : Prop :=
  match probe with
  | .owner id => left.ownerObservation id = right.ownerObservation id
  | .endpoint id => id ∈ left.endpoints ↔ id ∈ right.endpoints

/-- Ordered accepted observations and live authority agree; the underlying
claim lists (and any surrounding host journals) need not be equal. -/
structure State.LiveClaimsAgree {sig : Signature} (left right : State sig) : Prop where
  accepted : left.accepted = right.accepted
  owners : ∀ id, left.ownerObservation id = right.ownerObservation id
  endpoints : ∀ id, (id ∈ left.endpoints ↔ id ∈ right.endpoints)

/-- Cap the possible disagreements of the two actual writers by nominal identity.
Accepted indices still agree. An exceptional claim is not necessarily live on either side. -/
structure State.ClaimDiscrepancies {sig : Signature} (left right : State sig) (pending : Spend → Prop) : Prop where
  accepted : left.accepted = right.accepted
  observe : ∀ probe, ¬ pending probe → probe.ObservationAgrees left right

/-- Look up the nominal type and representation from the held receipt, not from the caller.
The result is a prospective update; the caller chooses when to commit it. -/
def State.prepare {sig : Signature} (state : State sig) (resource : RtId) (id : HandleObjId) :
    Except Issue (Nat × State sig) :=
  match state.held.find? (fun entry => receiptId entry == id) with
  | none => .error .unclaimed
  | some receipt =>
    if receipt.1 != resource then .error .wrongResourceType
    else .ok (receipt.2.representation, (Spend.owner id).apply state)

def State.spendEndpoint {sig : Signature} (state : State sig) (id : EndId) : Except Issue (State sig) :=
  if id ∈ state.endpoints then .ok ((Spend.endpoint id).apply state)
  else .error .unclaimedEndpoint

variable {E : CoreEngine}

structure Access (E : CoreEngine) (World : Type) (sig : Signature) where
  read : P E World (State sig)
  spend : Spend → P E World Unit

def Access.direct {sig : Signature} : Access E (State sig) sig :=
  ⟨hostGet, fun spend => do hostSet (spend.apply (← hostGet))⟩

/-- The shared canonical loader resolves owners and endpoints in one payload. Whole-schema
validation precedes lifting; a later trap does not publish any of the incomplete node's claims. -/
def acceptNode (sig : Signature) (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (tag : sig.Tag) (input : Input) (children : List (Tree sig)) :
    P E (State sig) (Except Issue (Tree sig)) := do
  match ← buildNode sig limits quirks cx tag input children with
  | .error issue => return .error (.lift issue)
  | .ok tree =>
    match (← hostGet).register tree with
    | .error issue => return .error issue
    | .ok registered =>
      hostSet registered
      return .ok tree

/-- Commit an already checked owner transfer immediately before canonical `lower_own`
allocates the new owning arena object. Insertion into the guest table can still trap;
this does not restore the claim or roll back the allocation. No guest code runs between
this commit and the allocation. -/
def commitOwner {World : Type} (spend : P E World Unit)
    (limits : Component.Limits) (cx : LiftLowerContext E) (resource : RtId)
    (representation : Nat) : P E World Nat := do
  spend
  lowerOwn limits cx resource representation

/-- Validate the nominal claim before committing a canonical owner transfer. -/
def Access.give {World : Type} {sig : Signature} (access : Access E World sig)
    (limits : Component.Limits) (cx : LiftLowerContext E) (resource : RtId) (id : HandleObjId) :
    P E World (Except Issue Nat) := do
  match (← access.read).prepare resource id with
  | .error issue => return .error issue
  | .ok (representation, _) =>
    return .ok (← commitOwner (access.spend (.owner id)) limits cx resource representation)

/-- Canonical lower of an endpoint can transfer its owner before a failing table insertion.
Commit spending before that effect, after validating the arena identity and whole element type. -/
def Access.giveEndpoint {World : Type} {sig : Signature} (access : Access E World sig)
    (limits : Component.Limits) (cx : LiftLowerContext E)
    (channel : Channel) (element : Element) (endpoint : Endpoint (channel.endKind .read) element) :
    P E World (Except Issue Nat) := do
  match (← access.read).spendEndpoint endpoint.id with
  | .error issue => return .error issue
  | .ok _ =>
    match Async.Transfer.readyToGive (← getStore) channel element endpoint with
    | .error issue => return .error (.endpointTransfer issue)
    | .ok () =>
      access.spend (.endpoint endpoint.id)
      return .ok (← lowerAsyncValue limits (channel.endKind .read) cx endpoint.id)

/-- Spend the host claim before entering the actual resource destructor, so a trapping
or reentrant destructor cannot make the same claim available a second time. -/
def Access.drop {World : Type} {sig : Signature} (access : Access E World sig)
    (destructor : InstId → DtorRequest E → P E World Unit) (resource : RtId) (id : HandleObjId) :
    P E World (Except Issue Unit) := do
  match (← access.read).prepare resource id with
  | .error issue => return .error issue
  | .ok (representation, _) =>
    let inst ← Builtins.resourceEnter
    let some request ← dropHandleTail resource { rt := resource, rep := representation, own := true }
      | internal "an owning resource drop must request its destructor"
    access.spend (.owner id)
    destructor inst request
    return .ok ()

def give {sig : Signature} (limits : Component.Limits) (cx : LiftLowerContext E)
    (resource : RtId) (id : HandleObjId) : P E (State sig) (Except Issue Nat) :=
  Access.direct.give limits cx resource id

def giveEndpoint {sig : Signature} (limits : Component.Limits) (cx : LiftLowerContext E)
    (channel : Channel) (element : Element) (endpoint : Endpoint (channel.endKind .read) element) :
    P E (State sig) (Except Issue Nat) :=
  Access.direct.giveEndpoint limits cx channel element endpoint

def drop {sig : Signature} (destructor : InstId → DtorRequest E → P E (State sig) Unit)
    (resource : RtId) (id : HandleObjId) : P E (State sig) (Except Issue Unit) :=
  Access.direct.drop destructor resource id

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims
