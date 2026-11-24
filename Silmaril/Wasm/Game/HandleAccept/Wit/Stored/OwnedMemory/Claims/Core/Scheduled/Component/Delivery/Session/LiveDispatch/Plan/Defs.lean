module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.LiveDispatch.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Correspondence.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Dispatch.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence.Traversal.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadCursor.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record.Observation.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LiveDispatch

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open ComponentCall.Delivery.FiniteSession
open Silmaril.Wasm.Game.HandleAccept.Wit.Async (Channel Element Channel.endKind)

variable {grow : SingleThreaded.GrowOracle} {sig : Signature}

/-- A raw host assignment is not a closed guest step. In particular, the
absence of a host read does not rule out an assignment installed by an open hook. -/
def NoHostAssignment (state : Config (core3 grow) (HostState sig)) : Prop :=
  ∀ thread value next frames rest,
    state.ctl ≠ ⟨thread, .prog (.op (.hostSet value) next), frames⟩ :: rest

/-- The checked writer commits these nominal spends in order. The raw canonical
writer has no corresponding authority updates. This describes writers, not
the rest of either host state or the canonical arena. -/
def CheckedSpendFlow (left right checked canonical : Stored.OwnedMemory.Claims.State sig)
    (spends : List Stored.OwnedMemory.Claims.Spend) : Prop :=
  checked = spends.foldl (fun state spend => spend.apply state) left ∧ canonical = right

abbrev WriterChange (sig : Signature) :=
  Stored.OwnedMemory.Claims.State sig × Stored.OwnedMemory.Claims.State sig

/-- This tests the actual writer delta. It does not identify the source of a
host assignment or authorize it as a guest spend. -/
def WriterChange.IsSpend (change : WriterChange sig) (spend : Stored.OwnedMemory.Claims.Spend) : Prop :=
  spend.Live change.1 ∧ change.2 = spend.apply change.1

def WriterChange.IsRegistration (change : WriterChange sig) (tree : Stored.OwnedMemory.Tree sig) : Prop :=
  change.1.register tree = .ok change.2

/-- Writer-changing steps in order, indexed by the complete machine trace.
An unchanged writer says nothing about the rest of the host. A write with
neither nominal delta is recorded, not treated as a journal-only update. -/
inductive WriterPath (profile : ProfileKind) (ready : HostReady (HostState sig))
    (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))) :
    Config (core3 grow) (HostState sig) → Trace grow sig → Config (core3 grow) (HostState sig) →
      List (WriterChange sig) → Prop where
  | done (state) : WriterPath profile ready dispatch state [] state []
  | same {start next finish label labels effects}
      (step : Step profile ready dispatch start label next)
      (unchanged : next.host.writer = start.host.writer)
      (tail : WriterPath profile ready dispatch next labels finish effects) :
      WriterPath profile ready dispatch start (label :: labels) finish effects
  | changed {start next finish label labels effects}
      (step : Step profile ready dispatch start label next)
      (different : next.host.writer ≠ start.host.writer)
      (tail : WriterPath profile ready dispatch next labels finish effects) :
      WriterPath profile ready dispatch start (label :: labels) finish ((start.host.writer, next.host.writer) :: effects)

/-- Separate ordered effects for the actual checked and fixed raw dispatches. -/
def PairedWriterPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (start incoming : Config (core3 grow) (HostState sig)) (checked canonical : Trace grow sig)
    (left right : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ leftEffects rightEffects,
    WriterPath profile ready (specDispatch ready base) start checked left leftEffects ∧
    WriterPath profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming canonical right rightEffects

/-- Control immediately after the loader's store write. Successful loading
leaves the registration read pending at the reached writer. -/
def coreAcceptAfterLoad (ticket : Nat) (result : Except Core.Issue (Stored.OwnedMemory.Tree sig)) :
    Session grow sig (Ret (core3 grow)) :=
  .flat <$> ((match result with
    | .error issue => pure (.error (.accept issue))
    | .ok tree => publishRoot ticket tree) >>= Scheduled.finish ticket)

/-- The loader's reached update and registration/refusal continuation,
prior to executing the store write. -/
def coreAcceptBeforeLoadWrite (ticket : Nat)
    (loaded : CStore (core3 grow) × Except Core.Issue (Stored.OwnedMemory.Tree sig)) :
    Session grow sig (Ret (core3 grow)) :=
  .op (.modify fun _ => loaded.1) fun _ => coreAcceptAfterLoad ticket loaded.2

structure CoreAcceptLoaderRead (profile : ProfileKind) (ready : HostReady (HostState sig))
    (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) (ticket : Nat)
    (loader : World grow sig → CStore (core3 grow) × Except Core.Issue (Stored.OwnedMemory.Tree sig))
    (before reached : Config (core3 grow) (HostState sig)) : Prop where
  entered : before.ctl = cursor.control (.flat <$> (do Scheduled.finish ticket (← acceptWith ticket loader)))
  pending : reached = { before with ctl := cursor.control (coreAcceptBeforeLoadWrite ticket
    (loader ⟨before.store, before.host.writer⟩)) }
  reads : Steps profile ready dispatch before [.tau, .tau] reached

/-- The linked publication read and its following executed registration
write. The trailing writer frames include any reached completion journal. -/
def ReachedRegistrationCommit (profile : ProfileKind) (ready : HostReady (HostState sig))
    (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (tree : Stored.OwnedMemory.Tree sig) (start : Config (core3 grow) (HostState sig))
    (labels : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ (ticket handle : Nat) (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)),
    ∃ probe committed next trailing,
    labels = [.tau, .tau] ++ trailing ∧
    (start.ctl = cursor.control (ComponentCall.completeResolvedTree ticket tree handle) ∨
      start.ctl = cursor.control (coreAcceptAfterLoad ticket (.ok tree))) ∧
    probe.ctl = cursor.control (.op (.hostSet committed.host) next) ∧
    Step profile ready dispatch start .tau probe ∧ Step profile ready dispatch probe .tau committed ∧
    probe.host = start.host ∧ probe.host.writer.register tree = .ok committed.host.writer ∧
    WriterPath profile ready dispatch committed trailing finish []

/-- The completion site's first read only probes. The following assignment
registers once; the remaining completion instructions only journal. -/
def ComponentPublicationWriterPrefix (profile : ProfileKind) (ready : HostReady (HostState sig))
    (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (tree : Stored.OwnedMemory.Tree sig) (start : Config (core3 grow) (HostState sig))
    (labels : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  if labels.length < 2 then WriterPath profile ready dispatch start labels finish []
  else WriterPath profile ready dispatch start labels finish [(start.host.writer, finish.host.writer)] ∧
    start.host.writer.register tree = .ok finish.host.writer ∧
    ReachedRegistrationCommit profile ready dispatch tree start labels finish

def PairedPublicationWriterPrefix (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (tree : Stored.OwnedMemory.Tree sig) (start incoming : Config (core3 grow) (HostState sig))
    (labels : Trace grow sig) (left right : Config (core3 grow) (HostState sig)) : Prop :=
  ComponentPublicationWriterPrefix profile ready (specDispatch ready base) tree start labels left ∧
    ComponentPublicationWriterPrefix profile ready (specDispatch ready (LiveDispatch.host bindings base)) tree incoming labels right

/-- The exact checked hostSet that commits a leaf spend and the framed
parts on either side of that instruction. -/
structure ReachedLeafSpend (profile : ProfileKind) (ready : HostReady (HostState sig))
    (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (start : Config (core3 grow) (HostState sig)) (checked : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig)) (change : WriterChange sig)
    (update : Stored.OwnedMemory.Claims.Spend) : Prop where
  live : change.IsSpend update
  site : ∃ leading trailing before after,
    checked = leading ++ [.tau] ++ trailing ∧
    WriterPath profile ready dispatch start leading before [] ∧
    LeafGuardSteps profile ready dispatch before [.tau] after (some update) ∧
    WriterPath profile ready dispatch after trailing finish [] ∧
    change = (before.host.writer, after.host.writer)

/-- A compiled leaf has no writer-changing raw step. On the checked side,
only the linked guard can change the writer, at its actual spend assignment. -/
def CompiledLeafWriterPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (start incoming : Config (core3 grow) (HostState sig)) (checked canonical : Trace grow sig)
    (left right : Config (core3 grow) (HostState sig)) (plan : Option Stored.OwnedMemory.Claims.Spend) : Prop :=
  CompiledLeafSource start plan ∧ ∃ changes, WriterPath profile ready (specDispatch ready base) start checked left changes ∧
    WriterPath profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming canonical right [] ∧
    (changes = [] ∨ ∃ change update, changes = [change] ∧ plan = some update ∧
      ReachedLeafSpend profile ready (specDispatch ready base) start checked left change update)

/-- The executed host assignment and its exact pre-write and post-write
configurations. Any earlier read is carried by its own writer path. -/
structure ReachedHostAssignment (profile : ProfileKind) (ready : HostReady (HostState sig))
    (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (before after : Config (core3 grow) (HostState sig)) : Prop where
  focus : ∃ thread frames rest target next,
    before.ctl = ⟨thread, .prog (.op (.hostSet target) next), frames⟩ :: rest ∧
    after = { before with host := target, ctl := ⟨thread, .prog (next ()), frames⟩ :: rest }
  step : Step profile ready dispatch before .tau after

/-- A compared open host assignment at the actual writes, with a writer
change on at least one side. -/
inductive CallbackWriterBoundary (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig)) :
    Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
    Trace grow sig → Trace grow sig → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) → Prop where
  | assignment {start incoming left right}
      (lhs : ReachedHostAssignment profile ready (specDispatch ready base) start left)
      (rhs : ReachedHostAssignment profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming right)
      (changed : left.host.writer ≠ start.host.writer ∨ right.host.writer ≠ incoming.host.writer) :
      CallbackWriterBoundary profile ready base bindings start incoming [.tau] [.tau] left right

/-- A registration probe does not commit the registration, even on a fresh result. -/
inductive ComponentRegistration where
  | aliased
  | exhausted
  | fresh (handle : Nat)

def componentRegistration (writer : Stored.OwnedMemory.Claims.State sig) (tree : Stored.OwnedMemory.Tree sig) :
    ComponentRegistration :=
  match writer.register tree with
  | .error _ => .aliased
  | .ok registered => if registered.accepted.length ≥ 2 ^ 32 then .exhausted else .fresh registered.accepted.length

def componentRegistrationProgram (ticket : Nat) (caller : CallerId) (tree : Stored.OwnedMemory.Tree sig) :
    ComponentRegistration → Session grow sig (Ret (core3 grow))
  | .aliased => ComponentCall.resolveRefused ticket caller (.accept (.claims .alias))
  | .exhausted => ComponentCall.reject ticket (.accept (.boundary .exhaustedHandles))
  | .fresh handle => do
    lowerOnResolve Limits.spec Quirks.none caller (some [.variant 0 (some (Value.Val.u32 handle))])
    ComponentCall.completeResolvedTree ticket tree handle

/-- The legacy Core registration selects its journal or commit from the
writer at the executed read. A fresh result still has a pending hostSet. -/
def coreAcceptRegistrationProgram (ticket : Nat) (tree : Stored.OwnedMemory.Tree sig) (current : HostState sig) :
    Session grow sig (Ret (core3 grow)) :=
  .flat <$> ((match current.writer.register tree with
    | .error issue => pure (.error (.accept (.claims issue)))
    | .ok writer => do
      let handle := writer.accepted.length
      if handle ≥ 2 ^ 32 then return .error (.accept (.boundary .exhaustedHandles))
      hostSet (({ current with writer } : HostState sig).record (.published ticket handle))
      return .ok handle) >>= Scheduled.finish ticket)

def registrationProbeProgram (caller : Option CallerId) (ticket : Nat) (tree : Stored.OwnedMemory.Tree sig) :
    Session grow sig (Ret (core3 grow)) :=
  match caller with
  | none => coreAcceptAfterLoad ticket (.ok tree)
  | some caller => ComponentCall.resolveTree ticket caller tree

def registrationAfterProbe (caller : Option CallerId) (ticket : Nat) (tree : Stored.OwnedMemory.Tree sig)
    (current : HostState sig) : Session grow sig (Ret (core3 grow)) :=
  match caller with
  | none => coreAcceptRegistrationProgram ticket tree current
  | some caller => componentRegistrationProgram ticket caller tree (componentRegistration current.writer tree)

/-- Distinct continuation programs selected by the two reached probes. -/
structure RegistrationProbeMismatch (beforeLeft beforeRight left right : Config (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (leftTicket rightTicket : Nat) (caller : Option CallerId) (tree : Stored.OwnedMemory.Tree sig) : Prop where
  leftFocus : beforeLeft.ctl = check.control (registrationProbeProgram caller leftTicket tree)
  rightFocus : beforeRight.ctl = canon.control (registrationProbeProgram caller rightTicket tree)
  leftProgram : left.ctl = check.control (registrationAfterProbe caller leftTicket tree left.host)
  rightProgram : right.ctl = canon.control (registrationAfterProbe caller rightTicket tree right.host)
  different : componentRegistration left.host.writer tree ≠ componentRegistration right.host.writer tree

open Stored.OwnedMemory.Claims in
/-- A requested live claim differs at the executed probe; history alone is not a disagreement. -/
def RegistrationConflict (left right : State sig) (tree : Stored.OwnedMemory.Tree sig) (pending : Spend → Prop) : Prop :=
  (∃ id ∈ (rootReceipts tree).map receiptId, pending (.owner id) ∧
    id ∉ (left.accepted.flatMap rootReceipts).map receiptId ∧
    ¬ ((Spend.owner id).Live left ↔ (Spend.owner id).Live right)) ∨
  (∃ id ∈ rootEndpoints tree, pending (.endpoint id) ∧
    ¬ ((Spend.endpoint id).Live left ↔ (Spend.endpoint id).Live right))

open Stored.OwnedMemory.Claims.Record in
/-- A checked prepare read compared against the writer of the pending raw
program. The raw path does not execute a prepare. -/
structure ExecutedPrepareRead (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig))
    (start reader left right : Config (core3 grow) (HostState sig)) (leading : Trace grow sig)
    (plan : List Stored.Endpoints.RecordLower.Object) : Prop where
  beforeRead : Steps profile ready (specDispatch ready base) start leading reader
  focus : ∃ (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (next : Except Stored.Endpoints.RecordLower.Issue Unit → Session grow sig (Ret (core3 grow))),
    reader.ctl = cursor.control (.op .hostGet (fun state => next (prepare reader.store state.writer plan)))
  read : Step profile ready (specDispatch ready base) reader .tau left
  writer : reader.host.writer = start.host.writer
  store : reader.store = right.store

open Stored.OwnedMemory.Claims.Record in
/-- Both dispatches execute the shared record's prepare. Each closure retains
its own completion continuation and the store read by its preceding get. -/
structure SharedRecordPrepareMismatch
    (left right reached peer : Config (core3 grow) (HostState sig))
    (plan : List Stored.Endpoints.RecordLower.Object)
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) where
  checkedNext : Except Stored.Endpoints.RecordLower.Issue Unit → Session grow sig (Ret (core3 grow))
  canonicalNext : Except Stored.Endpoints.RecordLower.Issue Unit → Session grow sig (Ret (core3 grow))
  store : left.store = right.store
  leftFocus : left.ctl = check.control (.op .hostGet (fun state => checkedNext (prepare left.store state.writer plan)))
  rightFocus : right.ctl = canon.control (.op .hostGet (fun state => canonicalNext (prepare right.store state.writer plan)))
  leftReached : reached.ctl = check.control (checkedNext (prepare left.store left.host.writer plan))
  rightReached : peer.ctl = canon.control (canonicalNext (prepare right.store right.host.writer plan))
  different : prepare left.store left.host.writer plan ≠ prepare right.store right.host.writer plan

/-- The four scheduled operations dispatched identically by both hosts.
The link fixes the resource or endpoint type before any guest argument is read. -/
inductive SharedGiveAction where
  | record (destination : RecordDestination)
  | giveOwner (resource : RtId)
  | dropOwner (resource : RtId)
  | endpoint (channel : Channel) (element : Element)

def SharedGiveAction.bindingAction (action : SharedGiveAction) : Action sig :=
  match action with
  | .record destination => .giveRecord destination
  | .giveOwner resource => .giveOwner resource
  | .dropOwner resource => .dropOwner resource
  | .endpoint channel element => .giveEndpoint channel element

def SharedGiveAction.selected (action : SharedGiveAction) (inst : InstId)
    (tree : Stored.OwnedMemory.Tree sig) (position : Nat) : Session grow sig (Except Scheduled.Issue Nat) := do
  let cx : LiftLowerContext (core3 grow) := { opts := {}, inst }
  match action with
  | .record dest =>
    return (← Stored.OwnedMemory.Claims.Record.lowerRoot recordClaims Limits.spec Quirks.none
      (dest.context inst) tree (.memory position)).mapError .lowerRecord |>.map (fun _ => 0)
  | .giveOwner resource =>
    let some receipt := (rootReceipts tree)[position]? | return .error .badSelection
    return (← claims.give Limits.spec cx resource (receiptId receipt)).mapError .claim
  | .dropOwner resource =>
    let some receipt := (rootReceipts tree)[position]? | return .error .badSelection
    let result ← claims.drop (destructorCall Limits.spec Quirks.none) resource (receiptId receipt)
    return result.mapError .claim |>.map (fun _ => 0)
  | .endpoint channel element =>
    let some id := (rootEndpoints tree)[position]? | return .error .badSelection
    return (← claims.giveEndpoint Limits.spec cx channel element ⟨id⟩).mapError .claim

/-- Select the reached tree and position, using a memory destination only for record give. -/
def SharedGiveAction.selection (action : SharedGiveAction) (args : List FlatValue) :
    Session grow sig (Except Scheduled.Issue (Stored.OwnedMemory.Tree sig × Nat)) := do
  match action with
  | .record dest => selectMemoryDestination dest args
  | _ =>
    let [.int .i32 handle, .int .i32 position] := args | return .error .wrongType
    let some tree ← select handle | return .error .badSelection
    return .ok (tree, position.toNat)

def SharedGiveAction.run (action : SharedGiveAction) (inst : InstId) (args : List FlatValue) :
    Session grow sig (Except Scheduled.Issue Nat) := do
  match ← action.selection args with
  | .error issue => return .error issue
  | .ok (tree, position) => action.selected inst tree position

def SharedGiveAction.afterLookup (action : SharedGiveAction) (inst : InstId) (ticket position : Nat)
    (found : Option (Stored.OwnedMemory.Tree sig)) : Session grow sig (Ret (core3 grow)) := do
  let some tree := found | return .flat (← Scheduled.finish ticket (.error .badSelection))
  return .flat (← Scheduled.finish ticket (← action.selected inst tree position))

/-- The linked action and selected root position determine which nominal
claim the scheduled body reads. The live writer supplies the owner representation. -/
inductive SharedGiveClaim where
  | giveOwner (resource : RtId) (identity : HandleObjId)
  | dropOwner (resource : RtId) (identity : HandleObjId)
  | endpoint (channel : Channel) (element : Element) (identity : EndId)

open Stored.OwnedMemory.Claims in
def SharedGiveClaim.demand : SharedGiveClaim → Spend
  | .giveOwner _ id | .dropOwner _ id => .owner id
  | .endpoint _ _ id => .endpoint id

def SharedGiveClaim.Permit : SharedGiveClaim → Type
  | .giveOwner .. | .dropOwner .. => Nat
  | .endpoint .. => Unit

open Stored.OwnedMemory.Claims in
def SharedGiveClaim.observe (claim : SharedGiveClaim) (writer : Stored.OwnedMemory.Claims.State sig) : Except Claims.Issue claim.Permit :=
  match claim with
  | .giveOwner resource id | .dropOwner resource id => (writer.prepare resource id).map Prod.fst
  | .endpoint _ _ id => (writer.spendEndpoint id).map (fun _ => ())

def SharedGiveAction.claimAt (action : SharedGiveAction) (tree : Stored.OwnedMemory.Tree sig) (position : Nat) :
    Option SharedGiveClaim :=
  match action with
  | .record _ => none
  | .giveOwner resource => ((rootReceipts tree)[position]?).map fun receipt => .giveOwner resource (receiptId receipt)
  | .dropOwner resource => ((rootReceipts tree)[position]?).map fun receipt => .dropOwner resource (receiptId receipt)
  | .endpoint channel element => ((rootEndpoints tree)[position]?).map fun id => .endpoint channel element id

open Stored.OwnedMemory.Claims in
def SharedGiveClaim.admitted (claim : SharedGiveClaim) (inst : InstId) (permit : claim.Permit) :
    Session grow sig (Except Scheduled.Issue Nat) :=
  let cx : LiftLowerContext (core3 grow) := { opts := {}, inst }
  match claim with
  | .giveOwner resource id => do
    return .ok (← commitOwner (claims.spend (.owner id)) Limits.spec cx resource permit)
  | .dropOwner resource id => do
    let caller ← Builtins.resourceEnter
    let some request ← dropHandleTail resource { rt := resource, rep := permit, own := true }
      | internal "an owning resource drop must request its destructor"
    claims.spend (.owner id)
    destructorCall Limits.spec Quirks.none caller request
    return .ok 0
  | .endpoint channel element id => do
    match Async.Transfer.readyToGive (← getStore) channel element ⟨id⟩ with
    | .error issue => return .error (.claim (.endpointTransfer issue))
    | .ok () =>
      claims.spend (.endpoint id)
      return .ok (← lowerAsyncValue Limits.spec (channel.endKind .read) cx id)

def SharedGiveClaim.afterRead (claim : SharedGiveClaim) (inst : InstId) (ticket : Nat)
    (observed : Except Claims.Issue claim.Permit) : Session grow sig (Ret (core3 grow)) := do
  let result ← match observed with
    | .error issue => pure (.error (.claim issue))
    | .ok permit => claim.admitted inst permit
  return .flat (← Scheduled.finish ticket result)

def SharedGiveClaim.probe (claim : SharedGiveClaim) (inst : InstId) (ticket : Nat) :
    Session grow sig (Ret (core3 grow)) :=
  .op .hostGet (fun current => claim.afterRead inst ticket (claim.observe current.writer))

/-- Both scheduled guards execute hostGet. The permit on each side is
computed from that side's reached live writer. -/
structure SharedGiveProbeMismatch (claim : SharedGiveClaim) (inst : InstId) (leftTicket rightTicket : Nat)
    (beforeLeft beforeRight left right : Config (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) : Prop where
  leftFocus : beforeLeft.ctl = check.control (claim.probe inst leftTicket)
  rightFocus : beforeRight.ctl = canon.control (claim.probe inst rightTicket)
  leftProgram : left.ctl = check.control (claim.afterRead inst leftTicket (claim.observe left.host.writer))
  rightProgram : right.ctl = canon.control (claim.afterRead inst rightTicket (claim.observe right.host.writer))
  different : claim.observe left.host.writer ≠ claim.observe right.host.writer

/-- Parameters fixed by the shared endpoint link and selected accepted root. -/
structure SharedEndpointGive where
  channel : Channel
  element : Element
  identity : EndId
  inst : InstId

def SharedEndpointGive.claim (site : SharedEndpointGive) : SharedGiveClaim :=
  .endpoint site.channel site.element site.identity

def SharedEndpointGive.transfer (site : SharedEndpointGive) : Session grow sig Nat :=
  lowerAsyncValue Limits.spec (site.channel.endKind .read) { opts := {}, inst := site.inst } site.identity

def scheduledReply (ticket : Nat) (verdict : Except Scheduled.Issue Nat) : Session grow sig (Ret (core3 grow)) := do
  return .flat (← Scheduled.finish ticket verdict)

open Stored.Endpoints in
def sharedRecordReport (ticket : Nat) (result : Except RecordLower.Issue Unit) :
    Session grow sig (Ret (core3 grow)) :=
  scheduledReply ticket (result.mapError .lowerRecord |>.map (fun _ => 0))

open Stored.OwnedMemory.Claims Stored.Endpoints in
def sharedRecordEmit (cx : LiftLowerContext (core3 grow)) (type : Stored.TypeOf) (value : Value.Val)
    (fields : List RecordLower.Field) (ptr ticket : Nat) : Session grow sig (Ret (core3 grow)) :=
  (do
    let width ← ptrType cx
    if !Stored.Lower.fits Quirks.none cx.opts.encoding width type value then
      return .error (.preflight (.abi .allocationPrecondition))
    RecordLower.Internal.emitRecord Limits.spec Quirks.none cx
      (Record.authority recordClaims Limits.spec cx) width type fields (.memory ptr)) >>= sharedRecordReport ticket

open Stored.OwnedMemory.Claims Stored.Endpoints in
/-- The shared visitor at the exact cursor and field index reached after earlier siblings. -/
def sharedRecordMemory (mode : LinkedCallback.MemorySequence.Track) (cx : LiftLowerContext (core3 grow)) (width : AddrType)
    (fields : List RecordLower.Field) (cursor index : Nat)
    (next : Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow))) : Session grow sig (Ret (core3 grow)) :=
  let authority := Record.authority recordClaims Limits.spec cx
  (match mode with
    | .fields | .placedFields => RecordLower.Internal.runMemory Limits.spec Quirks.none cx authority width fields cursor index
    | .elements stride => RecordLower.Internal.runElements Limits.spec Quirks.none cx authority width fields stride cursor index) >>= next

open Stored.Endpoints LinkedCallback.MemorySequence in
def sharedRecordAfterField (mode : Track) (cx : LiftLowerContext (core3 grow)) (width : AddrType)
    (fields : List RecordLower.Field) (cursor index : Nat)
    (next : Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow))) :
    Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow))
  | .error issue => next (.error issue)
  | .ok () => sharedRecordMemory mode cx width fields cursor index next

open Stored.Endpoints in
def sharedRecordCollectionResult (cx : LiftLowerContext (core3 grow)) (width : AddrType)
    (count index dest ptr : Nat) : Except RecordLower.Issue Unit → Session grow sig (Except RecordLower.Issue Unit)
  | .error issue => .pure (.error (.nested index issue))
  | .ok () => ListLower.publish cx width ptr count (.memory dest) >>= fun published => .pure (.ok published)

open Stored.Endpoints in
/-- The source visitor's pending sibling programs below an aggregate,
collection, or sum child. -/
inductive SharedRecordJoin where
  | report
  | field (mode : LinkedCallback.MemorySequence.Track) (siblings : List RecordLower.Field)
      (cursor nextIndex parentIndex : Nat) (outer : SharedRecordJoin)
  | collection (mode : LinkedCallback.MemorySequence.Track) (siblings : List RecordLower.Field)
      (cursor nextIndex parentIndex count dest pointer : Nat) (outer : SharedRecordJoin)

open Stored.Endpoints in
def SharedRecordJoin.reply (cx : LiftLowerContext (core3 grow)) (width : AddrType) (ticket : Nat) :
    SharedRecordJoin → Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow))
  | .report => sharedRecordReport ticket
  | .field mode siblings cursor nextIndex parentIndex outer =>
    fun result => sharedRecordAfterField mode cx width siblings cursor nextIndex
      (outer.reply cx width ticket) (result.mapError (.nested parentIndex))
  | .collection mode siblings cursor nextIndex parentIndex count dest pointer outer =>
    fun result => sharedRecordCollectionResult cx width count parentIndex dest pointer result >>=
      sharedRecordAfterField mode cx width siblings cursor nextIndex (outer.reply cx width ticket)

open Stored.Endpoints in
def sharedRecordVisit (cx : LiftLowerContext (core3 grow)) (fields : List RecordLower.Field) (ptr ticket : Nat) :
    Option AddrType → Session grow sig (Ret (core3 grow))
  | none => sharedRecordReport ticket (.error (.preflight (.abi .allocationPrecondition)))
  | some width => sharedRecordMemory .fields cx width fields ptr 0 (sharedRecordReport ticket)

open Stored.OwnedMemory.Claims Stored.Endpoints in
/-- The selected collection continuation after the second prepare. -/
def sharedRecordAfterAllocationPrepare (cx : LiftLowerContext (core3 grow)) (width : AddrType)
    (element : Stored.TypeOf) (entries : List RecordLower.Field) (index dest ptr : Nat) :
    Except RecordLower.Issue Unit → Session grow sig (Except RecordLower.Issue Unit)
  | .error (.preflight issue) => pure (.error (.field index (.afterAllocation issue)))
  | .error issue => pure (.error (.nested index issue))
  | .ok () => do
    let authority := Record.authority recordClaims Limits.spec cx
    let area := ABI.layout width element
    match ← RecordLower.Internal.runElements Limits.spec Quirks.none cx authority width entries area.size ptr 0 with
    | .error issue => return .error (.nested index issue)
    | .ok () => return .ok (← ListLower.publish cx width ptr entries.length (.memory dest))

open Stored.OwnedMemory.Claims Stored.Endpoints in
/-- The shared collection field at the pointer validated against the reached store. -/
def sharedRecordAllocated (cx : LiftLowerContext (core3 grow)) (width : AddrType)
    (element : Stored.TypeOf) (entries : List RecordLower.Field) (index dest ptr : Nat) :
    Session grow sig (Except RecordLower.Issue Unit) :=
  (Record.authority recordClaims Limits.spec cx).prepare (RecordLower.Field.listObjects entries) >>=
    sharedRecordAfterAllocationPrepare cx width element entries index dest ptr

open Stored.Endpoints in
/-- The shared collection field after its actual pre-allocation prepare succeeded. -/
def sharedRecordAllocate (cx : LiftLowerContext (core3 grow)) (width : AddrType)
    (element : Stored.TypeOf) (entries : List RecordLower.Field) (index dest : Nat) :
    Session grow sig (Except RecordLower.Issue Unit) := do
  let ptr ← ListLower.allocateRange cx (ABI.layout width element) entries.length
  sharedRecordAllocated cx width element entries index dest ptr

def sharedRecordRange (cx : LiftLowerContext (core3 grow)) (area : ABI.Layout) (count : Nat) :
    Ret (core3 grow) → Session grow sig Nat
  | .nat ptr => validateListRange cx area count ptr
  | _ => internal "late-bound call: expected Ret.nat"

open Stored.Endpoints in
def sharedRecordAllocationResume (cx : LiftLowerContext (core3 grow)) (width : AddrType)
    (element : Stored.TypeOf) (entries : List RecordLower.Field) (index dest : Nat)
    (next : Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow))) :
    ReturnFrame.Continuation (core3 grow) (HostState sig) := fun result => do
  let ptr ← sharedRecordRange cx (ABI.layout width element) entries.length result
  next (← sharedRecordAllocated cx width element entries index dest ptr)

/-- The descriptor writes performed after the canonical string loop. -/
def sharedRecordStringDescriptor (cx : LiftLowerContext (core3 grow)) (tagged dest pointer : Nat) :
    Session grow sig Unit := do
  let size ← ptrSize cx
  writeMem cx dest (strWordBytes size pointer)
  writeMem cx (dest + size) (strWordBytes size tagged)

open Stored.Endpoints in
/-- Resume the actual canonical string loop at its reached pointer and remaining steps. -/
def sharedRecordStringRemaining (cx : LiftLowerContext (core3 grow))
    (steps : List ABI.StoreStep) (tagged dest pointer : Nat)
    (next : Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow))) :
    Session grow sig (Ret (core3 grow)) := do
  let begin ← runStoreSteps cx pointer steps
  sharedRecordStringDescriptor cx tagged dest begin
  next (.ok ())

open Stored.Endpoints in
/-- The canonical string plan selected by the actual emitter width read. -/
def sharedRecordStringPlan (cx : LiftLowerContext (core3 grow))
    (value : Value.StrVal) (dest : Nat) (next : Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (width : AddrType) : Session grow sig (Ret (core3 grow)) :=
  let plan := storePlanFor Quirks.none cx.opts.encoding width value
  sharedRecordStringRemaining cx plan.steps plan.taggedCodeUnits dest 0 next

open Stored.Endpoints in
/-- The actual program continuation installed at a shared string allocator call. -/
def sharedRecordStringResume (cx : LiftLowerContext (core3 grow)) (steps : List ABI.StoreStep) (tagged dest : Nat)
    (next : Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow))) :
    ReturnFrame.Continuation (core3 grow) (HostState sig)
  | .nat pointer => sharedRecordStringRemaining cx steps tagged dest pointer next
  | _ => internal "late-bound call: expected Ret.nat"

open Stored.Endpoints in
/-- The compiler's allocation sites in a shared record visitor. A string
site records the prefix of its selected encoding plan. -/
inductive SharedRecordAllocation where
  | collection (width : AddrType) (element : Stored.TypeOf) (entries : List RecordLower.Field)
      (index dest : Nat)
  | string (width : AddrType) (value : Value.StrVal) (dest : Nat) (prior : List ABI.StoreStep)
      (old : Option (Nat × Nat)) (alignment : ABI.Alignment) (size : Nat) (remaining : List ABI.StoreStep)

def SharedRecordAllocation.request : SharedRecordAllocation → ABI.ReallocRequest
  | .collection width element entries _ _ =>
    let area := ABI.layout width element
    ⟨0, 0, area.alignment.bytes, entries.length * area.size⟩
  | .string _ _ _ _ old alignment size _ =>
    let (pointer, length) := old.getD (0, 0)
    ⟨pointer, length, alignment.bytes, size⟩

open Stored.Endpoints in
def SharedRecordAllocation.compiled (cx : LiftLowerContext (core3 grow)) : SharedRecordAllocation → Prop
  | .collection _ _ entries _ _ => ∀ field ∈ entries, RecordLower.Field.Emitted field
  | .string width value _ prior old alignment size remaining =>
    let step := match old with
      | none => ABI.StoreStep.allocate alignment size
      | some (_, length) => .reallocate length alignment size
    (storePlanFor Quirks.none cx.opts.encoding width value).steps = prior ++ step :: remaining

open Stored.Endpoints in
def SharedRecordAllocation.resume (cx : LiftLowerContext (core3 grow))
    (next : Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow))) :
    SharedRecordAllocation → ReturnFrame.Continuation (core3 grow) (HostState sig)
  | .collection width element entries index dest => sharedRecordAllocationResume cx width element entries index dest next
  | .string width value dest _ _ _ _ remaining =>
    sharedRecordStringResume cx remaining (storePlanFor Quirks.none cx.opts.encoding width value).taggedCodeUnits dest next

def SharedRecordAllocation.call (site : SharedRecordAllocation) (cx : LiftLowerContext (core3 grow)) : Call (core3 grow) :=
  let request := site.request
  .reallocate cx request.oldPtr request.oldSize request.alignment request.newSize

def sharedRecordAllocatorFlatArgs (width : AddrType) (request : ABI.ReallocRequest) : List FlatValue :=
  [ptrFlat width request.oldPtr, ptrFlat width request.oldSize, ptrFlat width request.alignment, ptrFlat width request.newSize]

def sharedRecordAllocatorArgs (width : AddrType) (request : ABI.ReallocRequest) : List Value.Val :=
  let kind := ptrIntKind width
  [.int kind request.oldPtr, .int kind request.oldSize, .int kind request.alignment, .int kind request.newSize]

/-- These lookups connect the resumed allocator to the caller and task created
by its own source setup. Later thread registration can update the task. -/
structure SharedRecordAllocatorSource (cx : LiftLowerContext (core3 grow)) (request : ABI.ReallocRequest)
    (width : AddrType) (task : TaskId) (caller : CallerId) (store : CStore (core3 grow)) (result : Option Value.Val := none) : Prop where
  taskEntry : ∃ tk, ArenaField.tasks.get? store task = some tk ∧ tk.ft = reallocType width ∧
    tk.opts = {} ∧ tk.inst = cx.inst ∧ tk.caller = caller
  callerEntry : ArenaField.callers.get? store caller = some (.sub (.realloc (sharedRecordAllocatorArgs width request) result))

/-- Finish the canonical allocator after the original synchronous lift returns. -/
def sharedRecordAllocatorResult (cx : LiftLowerContext (core3 grow)) (caller : CallerId) :
    Session grow sig (Ret (core3 grow)) := do
  modifyStore LiftSt.decNestingSt
  modifyInst cx.inst (LiftSt.setMayLeave true)
  match ← getObj ArenaField.callers caller with
  | .sub (.realloc _ (some (.int _ n))) => return .nat n.toNat
  | _ => internal "reallocate: realloc did not resolve with a pointer"

def sharedRecordAllocatorLoopReply (cx : LiftLowerContext (core3 grow)) (caller : CallerId) :
    ReturnFrame.Continuation (core3 grow) (HostState sig)
  | .unit => sharedRecordAllocatorResult cx caller
  | _ => internal "late-bound call: expected Ret.unit"

/-- The allocator parent parked by the actual synchronous lift worker resume. -/
def sharedRecordAllocatorAfterResume (cx : LiftLowerContext (core3 grow)) (task : TaskId) (caller : CallerId) :
    Session grow sig (Ret (core3 grow)) := do
  callUnit (.loop (.syncLiftLoop task))
  sharedRecordAllocatorResult cx caller

def sharedRecordAllocatorAfterThread (cx : LiftLowerContext (core3 grow)) (task : TaskId) (caller : CallerId)
    (worker : ThreadId) : Session grow sig (Ret (core3 grow)) :=
  Thread.resume worker >>= fun _ => sharedRecordAllocatorAfterResume cx task caller

open Stored.Endpoints in
def sharedRecordOwnerTransfer (cx : LiftLowerContext (core3 grow)) (resource : RtId) (rep ptr : Nat) :
    Session grow sig (Except RecordLower.Issue Unit) := do
  let slot ← lowerOwn Limits.spec cx resource rep
  return .ok (← RecordLower.Internal.publishSlot cx slot (.memory ptr))

open Stored.OwnedMemory.Claims Stored.Endpoints in
def sharedRecordOwnerAfterProbe (cx : LiftLowerContext (core3 grow)) (receipt : Stored.OwnedMemory.Receipt)
    (index ptr : Nat) : Except RecordLower.Issue Nat → Session grow sig (Except RecordLower.Issue Unit)
  | .error issue => .pure (.error (.nested index issue))
  | .ok rep => claims.spend (.owner (receiptId receipt)) >>= fun _ => sharedRecordOwnerTransfer cx receipt.1 rep ptr

open Stored.OwnedMemory.Claims Stored.Endpoints in
/-- The reached owner field checks its nominal receipt on both dispatches.
Each post-read focus keeps the original field and caller continuation. -/
structure SharedRecordOwnerProbeMismatch
    (left right reached peer : Config (core3 grow) (HostState sig))
    (receipt : Stored.OwnedMemory.Receipt) (cx : LiftLowerContext (core3 grow)) (index ptr : Nat)
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) where
  checkedNext : Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow))
  canonicalNext : Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow))
  leftFocus : left.ctl = check.control (.op .hostGet (fun state =>
    sharedRecordOwnerAfterProbe cx receipt index ptr ((Record.prepareOwner state.writer receipt).map Prod.fst) >>= checkedNext))
  rightFocus : right.ctl = canon.control (.op .hostGet (fun state =>
    sharedRecordOwnerAfterProbe cx receipt index ptr ((Record.prepareOwner state.writer receipt).map Prod.fst) >>= canonicalNext))
  leftReached : reached.ctl = check.control
    (sharedRecordOwnerAfterProbe cx receipt index ptr ((Record.prepareOwner left.host.writer receipt).map Prod.fst) >>= checkedNext)
  rightReached : peer.ctl = canon.control
    (sharedRecordOwnerAfterProbe cx receipt index ptr ((Record.prepareOwner right.host.writer receipt).map Prod.fst) >>= canonicalNext)
  different : (Record.prepareOwner left.host.writer receipt).map Prod.fst ≠
    (Record.prepareOwner right.host.writer receipt).map Prod.fst

open Stored.OwnedMemory.Claims Stored.Endpoints in
/-- The owner-field guard and spend read execute before the actual host assignment.
The canonical handle allocation and publication are still pending at the endpoint. -/
structure ExecutedSharedRecordOwnerSpend (profile : ProfileKind) (ready : HostReady (HostState sig))
    (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (receipt : Stored.OwnedMemory.Receipt) (cx : LiftLowerContext (core3 grow)) (index ptr rep : Nat)
    (next : Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (start finish : Config (core3 grow) (HostState sig)) : Prop where
  executed : ∃ (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (guarded writing : Config (core3 grow) (HostState sig)) (spent : Stored.OwnedMemory.Claims.State sig),
    start.ctl = cursor.control (.op .hostGet (fun state =>
      sharedRecordOwnerAfterProbe cx receipt index ptr ((Record.prepareOwner state.writer receipt).map Prod.fst) >>= next)) ∧
    Record.prepareOwner start.host.writer receipt = .ok (rep, spent) ∧
    guarded = { start with ctl := cursor.control (sharedRecordOwnerAfterProbe cx receipt index ptr (.ok rep) >>= next) } ∧
    writing = { guarded with ctl := cursor.control (.op (.hostSet
      { guarded.host with writer := (Spend.owner (receiptId receipt)).apply guarded.host.writer })
      (fun _ => sharedRecordOwnerTransfer cx receipt.1 rep ptr >>= next)) } ∧
    finish = { writing with
      host := { writing.host with writer := (Spend.owner (receiptId receipt)).apply writing.host.writer }
      ctl := cursor.control (sharedRecordOwnerTransfer cx receipt.1 rep ptr >>= next) } ∧
    Step profile ready dispatch start .tau guarded ∧
    Step profile ready dispatch guarded .tau writing ∧
    Step profile ready dispatch writing .tau finish

open Stored.Endpoints in
def sharedRecordEndpointTransfer (site : SharedEndpointGive) (cx : LiftLowerContext (core3 grow)) (ptr : Nat) :
    Session grow sig (Except RecordLower.Issue Unit) := do
  let slot ← site.transfer
  return .ok (← RecordLower.Internal.publishSlot cx slot (.memory ptr))

open Stored.OwnedMemory.Claims Stored.Endpoints in
def sharedRecordEndpointAfterPrepare (site : SharedEndpointGive) (cx : LiftLowerContext (core3 grow))
    (index ptr : Nat) : Except RecordLower.Issue Unit → Session grow sig (Except RecordLower.Issue Unit)
  | .error issue => .pure (.error (.nested index issue))
  | .ok () => claims.spend (.endpoint site.identity) >>= fun _ => sharedRecordEndpointTransfer site cx ptr

open Stored.OwnedMemory.Claims Stored.Endpoints in
def sharedRecordEndpointPrepare (site : SharedEndpointGive) (store : CStore (core3 grow)) (writer : Stored.OwnedMemory.Claims.State sig) :
    Except RecordLower.Issue Unit :=
  Record.prepare store writer [.shared (.endpoint site.channel site.element site.identity)]

open Stored.Endpoints in
def sharedRecordEndpointRead (site : SharedEndpointGive) (cx : LiftLowerContext (core3 grow))
    (index ptr : Nat) (writer : Stored.OwnedMemory.Claims.State sig) : Session grow sig (Except RecordLower.Issue Unit) :=
  .op .get fun store => sharedRecordEndpointAfterPrepare site cx index ptr (sharedRecordEndpointPrepare site store writer)

open Stored.Endpoints in
/-- The compiled endpoint field captures the writer at hostGet. Its following
get runs the guard with that writer and the reached store. -/
structure ExecutedSharedRecordEndpointGuard (profile : ProfileKind) (ready : HostReady (HostState sig))
    (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (site : SharedEndpointGive) (cx : LiftLowerContext (core3 grow)) (index ptr : Nat)
    (next : Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (start captured finish : Config (core3 grow) (HostState sig))
    (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) : Prop where
  focus : start.ctl = cursor.control (.op .hostGet (fun state =>
    sharedRecordEndpointRead site cx index ptr state.writer >>= next))
  capture : captured = { start with
    ctl := cursor.control (sharedRecordEndpointRead site cx index ptr start.host.writer >>= next) }
  prepare : finish = { captured with
    ctl := cursor.control (sharedRecordEndpointAfterPrepare site cx index ptr
      (sharedRecordEndpointPrepare site captured.store start.host.writer) >>= next) }
  hostRead : Step profile ready dispatch start .tau captured
  storeRead : Step profile ready dispatch captured .tau finish

open Stored.Endpoints in
structure SharedRecordEndpointMismatch (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (site : SharedEndpointGive) (left right reached peer : Config (core3 grow) (HostState sig)) where
  cx : LiftLowerContext (core3 grow)
  index : Nat
  ptr : Nat
  check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)
  canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)
  checkedNext : Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow))
  canonicalNext : Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow))
  checkedRead : Config (core3 grow) (HostState sig)
  canonicalRead : Config (core3 grow) (HostState sig)
  checked : ExecutedSharedRecordEndpointGuard profile ready (specDispatch ready base)
    site cx index ptr checkedNext left checkedRead reached check
  canonical : ExecutedSharedRecordEndpointGuard profile ready (specDispatch ready (LiveDispatch.host bindings base))
    site cx index ptr canonicalNext right canonicalRead peer canon
  store : left.store = right.store
  different : sharedRecordEndpointPrepare site left.store left.host.writer ≠
    sharedRecordEndpointPrepare site right.store right.host.writer

open Stored.OwnedMemory.Claims Stored.Endpoints in
/-- The executed endpoint-field guard precedes a fresh spend read and the
actual assignment. Canonical transfer and publication follow this endpoint. -/
structure ExecutedSharedRecordEndpointSpend (profile : ProfileKind) (ready : HostReady (HostState sig))
    (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (site : SharedEndpointGive) (cx : LiftLowerContext (core3 grow)) (index ptr : Nat)
    (next : Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (start finish : Config (core3 grow) (HostState sig)) : Prop where
  executed : ∃ (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (captured prepared writing : Config (core3 grow) (HostState sig)) (spent : Stored.OwnedMemory.Claims.State sig),
    ExecutedSharedRecordEndpointGuard profile ready dispatch site cx index ptr next start captured prepared cursor ∧
    Record.prepareEndpoint captured.store start.host.writer site.channel site.element site.identity = .ok spent ∧
    writing = { prepared with ctl := cursor.control (.op (.hostSet
      { prepared.host with writer := (Spend.endpoint site.identity).apply prepared.host.writer })
      (fun _ => sharedRecordEndpointTransfer site cx ptr >>= next)) } ∧
    finish = { writing with
      host := { writing.host with writer := (Spend.endpoint site.identity).apply writing.host.writer }
      ctl := cursor.control (sharedRecordEndpointTransfer site cx ptr >>= next) } ∧
    Step profile ready dispatch prepared .tau writing ∧
    Step profile ready dispatch writing .tau finish

def SharedEndpointGive.afterSpend (site : SharedEndpointGive) (ticket : Nat) : Session grow sig (Ret (core3 grow)) :=
  site.transfer >>= fun idx => scheduledReply ticket (.ok idx)

def SharedEndpointGive.spend (site : SharedEndpointGive) (ticket : Nat) : Session grow sig (Ret (core3 grow)) :=
  claims.spend (.endpoint site.identity) >>= fun _ => site.afterSpend ticket

def SharedEndpointGive.afterReady (site : SharedEndpointGive) (ticket : Nat) (store : CStore (core3 grow)) :
    Session grow sig (Ret (core3 grow)) :=
  match Async.Transfer.readyToGive store site.channel site.element ⟨site.identity⟩ with
  | .error issue => scheduledReply ticket (.error (.claim (.endpointTransfer issue)))
  | .ok () => site.spend ticket

def SharedEndpointGive.checkedStore (site : SharedEndpointGive) (ticket : Nat) : Session grow sig (Ret (core3 grow)) :=
  .op .get (site.afterReady ticket)

open Stored.OwnedMemory.Claims in
/-- The scheduled endpoint transfer follows the reached live guard and
readiness read, then commits the spend with the real hostSet. -/
structure ExecutedSharedEndpointSpend (profile : ProfileKind) (ready : HostReady (HostState sig))
    (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (site : SharedEndpointGive) (ticket : Nat)
    (start finish : Config (core3 grow) (HostState sig)) : Prop where
  executed : ∃ (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (guarded prepared writing : Config (core3 grow) (HostState sig)),
    start.ctl = cursor.control (site.claim.probe site.inst ticket) ∧
    site.identity ∈ start.host.writer.endpoints ∧
    Async.Transfer.readyToGive start.store site.channel site.element ⟨site.identity⟩ = .ok () ∧
    guarded = { start with ctl := cursor.control (site.checkedStore ticket) } ∧
    prepared = { guarded with ctl := cursor.control (site.spend ticket) } ∧
    writing = { prepared with ctl := cursor.control (.op (.hostSet
      { prepared.host with writer := (Spend.endpoint site.identity).apply prepared.host.writer })
      (fun _ => site.afterSpend ticket)) } ∧
    finish = { writing with
      host := { writing.host with writer := (Spend.endpoint site.identity).apply writing.host.writer }
      ctl := cursor.control (site.afterSpend ticket) } ∧
    Step profile ready dispatch start .tau guarded ∧
    Step profile ready dispatch guarded .tau prepared ∧
    Step profile ready dispatch prepared .tau writing ∧
    Step profile ready dispatch writing .tau finish

/-- The linked owner give fixes the type and the selected arena identity.
Its representation comes from the live prepare on each side. -/
structure SharedOwnerGive where
  resource : RtId
  identity : HandleObjId
  inst : InstId

def SharedOwnerGive.claim (site : SharedOwnerGive) : SharedGiveClaim :=
  .giveOwner site.resource site.identity

def SharedOwnerGive.transfer (site : SharedOwnerGive) (rep : Nat) : Session grow sig Nat :=
  lowerOwn Limits.spec { opts := {}, inst := site.inst } site.resource rep

def SharedOwnerGive.afterSpend (site : SharedOwnerGive) (rep ticket : Nat) : Session grow sig (Ret (core3 grow)) :=
  site.transfer rep >>= fun idx => scheduledReply ticket (.ok idx)

def SharedOwnerGive.spend (site : SharedOwnerGive) (rep ticket : Nat) : Session grow sig (Ret (core3 grow)) :=
  claims.spend (.owner site.identity) >>= fun _ => site.afterSpend rep ticket

open Stored.OwnedMemory.Claims in
/-- The reached owner prepare authorizes the spend read and its actual hostSet
before canonical lowering allocates a fresh handle. -/
structure ExecutedSharedOwnerSpend (profile : ProfileKind) (ready : HostReady (HostState sig))
    (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (site : SharedOwnerGive) (rep ticket : Nat)
    (start finish : Config (core3 grow) (HostState sig)) : Prop where
  executed : ∃ (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (prepared writing : Config (core3 grow) (HostState sig)) (spent : Stored.OwnedMemory.Claims.State sig),
    start.ctl = cursor.control (site.claim.probe site.inst ticket) ∧
    start.host.writer.prepare site.resource site.identity = .ok (rep, spent) ∧
    prepared = { start with ctl := cursor.control (site.spend rep ticket) } ∧
    writing = { prepared with ctl := cursor.control (.op (.hostSet
      { prepared.host with writer := (Spend.owner site.identity).apply prepared.host.writer })
      (fun _ => site.afterSpend rep ticket)) } ∧
    finish = { writing with
      host := { writing.host with writer := (Spend.owner site.identity).apply writing.host.writer }
      ctl := cursor.control (site.afterSpend rep ticket) } ∧
    Step profile ready dispatch start .tau prepared ∧
    Step profile ready dispatch prepared .tau writing ∧
    Step profile ready dispatch writing .tau finish

/-- The linked owner drop and the selected root fix the type and arena identity.
The representation still comes from the live prepare on each side. -/
structure SharedOwnerDrop where
  resource : RtId
  identity : HandleObjId
  inst : InstId

def SharedOwnerDrop.claim (site : SharedOwnerDrop) : SharedGiveClaim :=
  .dropOwner site.resource site.identity

/-- The owning branch of the scheduled drop tail looks up the resource type
in the reached store and produces the actual destructor request. -/
def SharedOwnerDrop.prepare (site : SharedOwnerDrop) (rep : Nat) :
    Session grow sig (InstId × DtorRequest (core3 grow)) := do
  let caller ← Builtins.resourceEnter
  let rty ← getResourceType site.resource
  return (caller, { rt := site.resource, impl := rty.impl, dtor := rty.dtor, rep := rep })

def SharedOwnerDrop.afterSpend (ticket : Nat) (result : InstId × DtorRequest (core3 grow)) :
    Session grow sig (Ret (core3 grow)) := do
  destructorCall Limits.spec Quirks.none result.1 result.2
  scheduledReply ticket (.ok 0)

def SharedOwnerDrop.spend (site : SharedOwnerDrop) (ticket : Nat) (result : InstId × DtorRequest (core3 grow)) :
    Session grow sig (Ret (core3 grow)) :=
  claims.spend (.owner site.identity) >>= fun _ => SharedOwnerDrop.afterSpend ticket result

open Stored.OwnedMemory.Claims in
/-- The nominal prepare, executed store checks and spend read precede the
actual hostSet. The reached request is retained in the destructor program. -/
structure ExecutedSharedDropSpend (profile : ProfileKind) (ready : HostReady (HostState sig))
    (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (site : SharedOwnerDrop) (rep ticket : Nat) (result : InstId × DtorRequest (core3 grow))
    (preparation : Trace grow sig) (start finish : Config (core3 grow) (HostState sig)) : Prop where
  executed : ∃ (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (guarded prepared writing : Config (core3 grow) (HostState sig)) (spent : Stored.OwnedMemory.Claims.State sig),
    start.ctl = cursor.control (site.claim.probe site.inst ticket) ∧
    start.host.writer.prepare site.resource site.identity = .ok (rep, spent) ∧
    guarded = { start with ctl := cursor.control (site.prepare rep >>= site.spend ticket) } ∧
    prepared.ctl = cursor.control (site.spend ticket result) ∧
    writing = { prepared with ctl := cursor.control (.op (.hostSet
      { prepared.host with writer := (Spend.owner site.identity).apply prepared.host.writer })
      (fun _ => SharedOwnerDrop.afterSpend ticket result)) } ∧
    finish = { writing with
      host := { writing.host with writer := (Spend.owner site.identity).apply writing.host.writer }
      ctl := cursor.control (SharedOwnerDrop.afterSpend ticket result) } ∧
    Step profile ready dispatch start .tau guarded ∧
    WriterPath profile ready dispatch guarded preparation prepared [] ∧
    Step profile ready dispatch prepared .tau writing ∧
    Step profile ready dispatch writing .tau finish

def sharedDestructorThread (task : TaskId) (callee : Option (core3 grow).FuncAddr) : ThreadBody (core3 grow) :=
  match callee with
  | some callee => .liftImplicit task callee
  | none => .liftNoop task

def sharedDestructorArguments (task : TaskId) (callee : Option (core3 grow).FuncAddr)
    (tk : Task (core3 grow)) (args : List Value.Val) : Session grow sig (Ret (core3 grow)) :=
  match callee with
  | some callee => liftArgumentsBody Limits.spec Quirks.none task callee tk args
  | none => do
    let cx : LiftLowerContext (core3 grow) := { opts := tk.opts, inst := tk.inst, scope := .task task }
    let _ ← lowerFlatValues Limits.spec Quirks.none cx ABI.maxFlatParams args (paramTypes tk.ft) none
    let (result, _) ← liftFlatValues Limits.spec Quirks.none cx ABI.maxFlatResults (.ofList []) (resultTypes tk.ft)
    Task.return_ task result
    Task.exitImplicitThread task
    return .unit

def sharedDestructorStartReply (task : TaskId) (callee : Option (core3 grow).FuncAddr)
    (tk : Task (core3 grow)) : ReturnFrame.Continuation (core3 grow) (HostState sig)
  | .vals args => sharedDestructorArguments task callee tk args
  | _ => internal "late-bound call: expected Ret.vals"

def sharedDestructorFlatArgument (width : AddrType) (rep : Nat) : FlatValue :=
  lowerFlatInt (match width with | .i32 => .u32 | .i64 => .u64) rep

def sharedDestructorFinish (task : TaskId) (values : List Value.Val) : Session grow sig (Ret (core3 grow)) := do
  Task.return_ task values
  Task.exitImplicitThread task
  return .unit

def sharedDestructorResolveReply (task : TaskId) : ReturnFrame.Continuation (core3 grow) (HostState sig)
  | .unit => do
    modifyStore (CStore.setTaskState task .resolved)
    Task.exitImplicitThread task
    return .unit
  | _ => internal "late-bound call: expected Ret.unit"

def sharedDestructorCoreResult (task : TaskId) (tk : Task (core3 grow)) (flat : List FlatValue) :
    Session grow sig (Ret (core3 grow)) := do
  let cx : LiftLowerContext (core3 grow) := { opts := tk.opts, inst := tk.inst, scope := .task task }
  let (values, _) ← liftFlatValues Limits.spec Quirks.none cx ABI.maxFlatResults (.ofList flat) (resultTypes tk.ft)
  sharedDestructorFinish task values

def sharedDestructorBodyFocus (task : TaskId) (callee : Option (core3 grow).FuncAddr) (tk : Task (core3 grow))
    (width : AddrType) (rep : Nat) : Focus (core3 grow) (HostState sig) :=
  match callee with
  | none => .prog (sharedDestructorFinish task [])
  | some f => .core ((core3 grow).invoke f [sharedDestructorFlatArgument width rep]) (sharedDestructorCoreResult task tk)

def sharedDestructorAfterAdmission (task : TaskId) (callee : Option (core3 grow).FuncAddr) :
    Bool → Session grow sig (Ret (core3 grow))
  | false => .pure .unit
  | true =>
    match callee with
    | some callee => do
      let tk ← getTask task
      let args ← Task.start task
      liftArgumentsBody Limits.spec Quirks.none task callee tk args
    | none => do
      let tk ← getTask task
      let cx : LiftLowerContext (core3 grow) := { opts := tk.opts, inst := tk.inst, scope := .task task }
      let args ← Task.start task
      let _ ← lowerFlatValues Limits.spec Quirks.none cx ABI.maxFlatParams args (paramTypes tk.ft) none
      let (result, _) ← liftFlatValues Limits.spec Quirks.none cx ABI.maxFlatResults (.ofList []) (resultTypes tk.ft)
      Task.return_ task result
      Task.exitImplicitThread task
      return .unit

def sharedDestructorAfterTaskRead (task : TaskId) (callee : Option (core3 grow).FuncAddr) (worker : ThreadId)
    (store : CStore (core3 grow)) : Session grow sig (Ret (core3 grow)) :=
  match ArenaField.tasks.get? store task with
  | none => internal "dangling arena id"
  | some tk => do
    let entered ← (if tk.ft.async_ then Task.asyncGate Quirks.none task worker tk else pure true : Session grow sig Bool)
    ((if entered then (Task.registerThread task worker).bind fun _ => .pure true
      else .pure false) : Session grow sig Bool).bind (sharedDestructorAfterAdmission task callee)

def sharedDestructorAfterThreadRead (task : TaskId) (callee : Option (core3 grow).FuncAddr) :
    Option ThreadId → Session grow sig (Ret (core3 grow))
  | none => internal "no current thread"
  | some worker => .op (.modify (CStore.setImplicitThread task worker))
      (fun _ => .op .get (sharedDestructorAfterTaskRead task callee worker))

/-- Read the representation used by the source destructor after its actual
instance and resource checks. -/
def sharedDestructorResourceRep (result : InstId × DtorRequest (core3 grow)) : Session grow sig AddrType := do
  let st ← getInst result.1
  trapIf (!st.mayLeave) .cannotLeave
  let rty ← getObj ArenaField.resourceTypes result.2.rt
  return rty.rep

/-- Construct the task from the representation and the allocated caller. The
function type is synchronous independently of the representation. -/
def sharedDestructorTaskRecord (impl : InstId) (rep : AddrType) (caller : CallerId) :
    { entry : Task (core3 grow) // entry.ft.async_ = false } :=
  ⟨{ ft := dtorType rep, opts := {}, inst := impl, caller }, rfl⟩

def sharedDestructorTaskDescription (result : InstId × DtorRequest (core3 grow)) (impl : InstId) :
    Session grow sig { entry : Task (core3 grow) // entry.ft.async_ = false } := do
  let rep ← sharedDestructorResourceRep result
  let caller ← allocObj ArenaField.callers (Caller.sub (.destructor result.2.rep) : Caller (core3 grow))
  return sharedDestructorTaskRecord impl rep caller

def sharedDestructorTask (result : InstId × DtorRequest (core3 grow)) (impl : InstId) :
    Session grow sig TaskId := do
  let entry ← sharedDestructorTaskDescription result impl
  allocObj ArenaField.tasks entry.val

/-- The store-only prefix of the canonical destructor determines the worker
body and its task. A host resource needs no worker. -/
def sharedDestructorWorker (result : InstId × DtorRequest (core3 grow)) :
    Session grow sig (Option (ThreadBody (core3 grow))) :=
  match result.2.impl with
  | none => pure none
  | some impl => sharedDestructorTask result impl >>= fun task => pure (some (sharedDestructorThread task result.2.dtor))

/-- Dispatch the result of the parent loop into the source completion journal. -/
def sharedDestructorParentReply (ticket : Nat) : ReturnFrame.Continuation (core3 grow) (HostState sig)
  | .unit => scheduledReply ticket (.ok 0)
  | _ => internal "late-bound call: expected Ret.unit"

/-- The suspended parent runs the same synchronous lift loop with its own
completion ticket after the actual worker resume. -/
def sharedDestructorAfterResume (body : ThreadBody (core3 grow)) (ticket : Nat) :
    Session grow sig (Ret (core3 grow)) := do
  callUnit (.loop (.syncLiftLoop body.task))
  scheduledReply ticket (.ok 0)

def sharedDestructorAfterInstall (body : ThreadBody (core3 grow)) (ticket : Nat) (thread : ThreadId) :
    Session grow sig (Ret (core3 grow)) := do
  Thread.resume thread
  sharedDestructorAfterResume body ticket

def sharedDestructorStart (ticket : Nat) (worker : Option (ThreadBody (core3 grow))) :
    Session grow sig (Ret (core3 grow)) :=
  match worker with
  | none => scheduledReply ticket (.ok 0)
  | some body => .op (.newThread body) (sharedDestructorAfterInstall body ticket)

/-- The actual allocation saves the dispatched worker in the reached arena
slot. The active parent remains at its own resume program. -/
structure SharedDestructorInstalled (profile : ProfileKind) (ready : HostReady (HostState sig))
    (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (body : ThreadBody (core3 grow)) (ticket : Nat) (thread : ThreadId)
    (before after : Config (core3 grow) (HostState sig))
    (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) : Prop where
  focus : before.ctl = cursor.control (sharedDestructorStart ticket (some body))
  allocated : ArenaField.threads.alloc before.store { task := body.task } = (after.store, thread)
  step : Step profile ready dispatch before .tau after
  saved : after.cont? thread = some (StepDefs.threadAct dispatch thread body)
  parent : after.ctl = cursor.control (sharedDestructorAfterInstall body ticket thread)

/-- The original reached worker inherits its actual saved activation. The
left and right paused parents retain their own continuations. -/
structure SharedDestructorResumed (profile : ProfileKind) (ready : HostReady (HostState sig))
    (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (body : ThreadBody (core3 grow)) (ticket : Nat) (thread : ThreadId)
    (before after : Config (core3 grow) (HostState sig))
    (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) : Prop where
  focus : before.ctl = cursor.control (.op (.resumeThread thread) (fun _ => sharedDestructorAfterResume body ticket))
  saved : before.cont? thread = some (StepDefs.threadAct dispatch thread body)
  step : Step profile ready dispatch before .tau after
  active : after.ctl = StepDefs.threadAct dispatch thread body ::
    cursor.control (sharedDestructorAfterResume body ticket)

/-- The arena endpoints and buffers selected by the copy's store read. -/
def CopyTransferOrigin (endpoint : EndId) (buffer : BufferDesc (core3 grow)) (reading : Bool)
    (store : CStore (core3 grow)) : CopyAction (core3 grow) → Prop
  | .none => False
  | .transfer writer reader count writerBuffer readerBuffer =>
    ∃ selected peer peerEnd peerBuffer,
      store.end? endpoint = some selected ∧ selected.other = some peer ∧ peer ≠ endpoint ∧
      store.end? peer = some peerEnd ∧ peerEnd.buffer = some peerBuffer ∧
      count = min buffer.remain peerBuffer.remain ∧ 0 < count ∧
      (if reading then
        writer = peer ∧ reader = endpoint ∧ writerBuffer = peerBuffer ∧ readerBuffer = buffer
       else
        writer = endpoint ∧ reader = peer ∧ writerBuffer = buffer ∧ readerBuffer = peerBuffer)

/-- The read has installed the selected bookkeeping and buffer program. -/
def copyTransferRead (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (before : Config (core3 grow) (HostState sig)) (endpoint : EndId) (buffer : BufferDesc (core3 grow))
    (reading : Bool) (action : CopyAction (core3 grow)) (next : Session grow sig (Ret (core3 grow))) :
    Config (core3 grow) (HostState sig) :=
  { before with ctl := cursor.control (do
      modifyStore (copySt endpoint buffer reading)
      performCopy Limits.spec Quirks.none action
      next) }

/-- Executing the copy read and commit leaves the selected buffer action
pending above the original continuation. -/
structure ExecutedCopyTransfer (profile : ProfileKind) (ready : HostReady (HostState sig))
    (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) (endpoint : EndId)
    (buffer : BufferDesc (core3 grow)) (reading : Bool) (action : CopyAction (core3 grow))
    (next : Session grow sig (Ret (core3 grow))) (before after : Config (core3 grow) (HostState sig)) : Prop where
  focus : before.ctl = cursor.control (endCopy Limits.spec Quirks.none endpoint buffer reading >>= fun _ => next)
  selected : copyCore endpoint buffer reading before.store = .ok (after.store, action)
  origin : CopyTransferOrigin endpoint buffer reading before.store action
  read : Step profile ready dispatch before .tau (copyTransferRead cursor before endpoint buffer reading action next)
  commit : Step profile ready dispatch (copyTransferRead cursor before endpoint buffer reading action next) .tau after
  reached : after = { before with
    store := after.store
    ctl := cursor.control (performCopy Limits.spec Quirks.none action >>= fun _ => next) }

/-- Ordered evidence on the actual pair of visited program segments.
Compiled guards and shared scheduled commits identify the source of nominal spends. -/
inductive VisitorWriterPath (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig)) :
    Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
    Trace grow sig → Trace grow sig → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) → Prop where
  | framed {start incoming checked canonical left right}
      (lhs : WriterPath profile ready (specDispatch ready base) start checked left [])
      (rhs : WriterPath profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming canonical right []) :
      VisitorWriterPath profile ready base bindings start incoming checked canonical left right
  | prepare {start incoming reader leading canonical left right plan}
      (site : ExecutedPrepareRead profile ready base start reader left right leading plan)
      (lhs : WriterPath profile ready (specDispatch ready base) start (leading ++ [.tau]) left [])
      (rhs : WriterPath profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming canonical right []) :
      VisitorWriterPath profile ready base bindings start incoming (leading ++ [.tau]) canonical left right
  | registrationMismatch {start incoming left right check canon leftTicket rightTicket caller tree}
      (site : RegistrationProbeMismatch start incoming left right check canon leftTicket rightTicket caller tree)
      (lhs : WriterPath profile ready (specDispatch ready base) start [.tau] left [])
      (rhs : WriterPath profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming [.tau] right []) :
      VisitorWriterPath profile ready base bindings start incoming [.tau] [.tau] left right
  | sharedGiveMismatch {start incoming left right check canon leftTicket rightTicket inst claim}
      (site : SharedGiveProbeMismatch claim inst leftTicket rightTicket start incoming left right check canon)
      (lhs : WriterPath profile ready (specDispatch ready base) start [.tau] left [])
      (rhs : WriterPath profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming [.tau] right []) :
      VisitorWriterPath profile ready base bindings start incoming [.tau] [.tau] left right
  | sharedRecordPrepare {start incoming left right check canon plan}
      (site : SharedRecordPrepareMismatch start incoming left right plan check canon)
      (lhs : WriterPath profile ready (specDispatch ready base) start [.tau] left [])
      (rhs : WriterPath profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming [.tau] right []) :
      VisitorWriterPath profile ready base bindings start incoming [.tau] [.tau] left right
  | recordOwnerMismatch {start incoming left right receipt cx index ptr check canon}
      (site : SharedRecordOwnerProbeMismatch start incoming left right receipt cx index ptr check canon)
      (lhs : WriterPath profile ready (specDispatch ready base) start [.tau] left [])
      (rhs : WriterPath profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming [.tau] right []) :
      VisitorWriterPath profile ready base bindings start incoming [.tau] [.tau] left right
  | recordEndpointMismatch {start incoming left right site}
      (mismatch : SharedRecordEndpointMismatch profile ready base bindings site start incoming left right) :
      VisitorWriterPath profile ready base bindings start incoming [.tau, .tau] [.tau, .tau] left right
  | recordEndpointCommit {start incoming left right site cx index ptr checkedNext canonicalNext}
      (lhs : ExecutedSharedRecordEndpointSpend profile ready (specDispatch ready base) site cx index ptr checkedNext start left)
      (rhs : ExecutedSharedRecordEndpointSpend profile ready (specDispatch ready (LiveDispatch.host bindings base))
        site cx index ptr canonicalNext incoming right) :
      VisitorWriterPath profile ready base bindings start incoming [.tau, .tau, .tau, .tau] [.tau, .tau, .tau, .tau] left right
  | recordOwnerCommit {start incoming left right receipt cx index ptr rep checkedNext canonicalNext}
      (lhs : ExecutedSharedRecordOwnerSpend profile ready (specDispatch ready base) receipt cx index ptr rep checkedNext start left)
      (rhs : ExecutedSharedRecordOwnerSpend profile ready (specDispatch ready (LiveDispatch.host bindings base))
        receipt cx index ptr rep canonicalNext incoming right) :
      VisitorWriterPath profile ready base bindings start incoming [.tau, .tau, .tau] [.tau, .tau, .tau] left right
  | ownerCommit {start incoming left right site rep leftTicket rightTicket}
      (lhs : ExecutedSharedOwnerSpend profile ready (specDispatch ready base) site rep leftTicket start left)
      (rhs : ExecutedSharedOwnerSpend profile ready (specDispatch ready (LiveDispatch.host bindings base)) site rep rightTicket incoming right) :
      VisitorWriterPath profile ready base bindings start incoming [.tau, .tau, .tau] [.tau, .tau, .tau] left right
  | dropCommit {start incoming left right site rep leftTicket rightTicket result preparation}
      (lhs : ExecutedSharedDropSpend profile ready (specDispatch ready base) site rep leftTicket result preparation start left)
      (rhs : ExecutedSharedDropSpend profile ready (specDispatch ready (LiveDispatch.host bindings base))
        site rep rightTicket result preparation incoming right) :
      VisitorWriterPath profile ready base bindings start incoming
        (.tau :: (preparation ++ [.tau, .tau])) (.tau :: (preparation ++ [.tau, .tau])) left right
  | endpointCommit {start incoming left right site leftTicket rightTicket}
      (lhs : ExecutedSharedEndpointSpend profile ready (specDispatch ready base) site leftTicket start left)
      (rhs : ExecutedSharedEndpointSpend profile ready (specDispatch ready (LiveDispatch.host bindings base)) site rightTicket incoming right) :
      VisitorWriterPath profile ready base bindings start incoming [.tau, .tau, .tau, .tau] [.tau, .tau, .tau, .tau] left right
  | copyTransfer {start incoming left right check canon endpoint buffer reading action next}
      (lhs : ExecutedCopyTransfer profile ready (specDispatch ready base) check endpoint buffer reading action next start left)
      (rhs : ExecutedCopyTransfer profile ready (specDispatch ready (LiveDispatch.host bindings base))
        canon endpoint buffer reading action next incoming right) :
      VisitorWriterPath profile ready base bindings start incoming [.tau, .tau] [.tau, .tau] left right
  | guarded {start incoming checked canonical left right plan}
      (paths : CompiledLeafWriterPaths profile ready base bindings start incoming checked canonical left right plan) :
      VisitorWriterPath profile ready base bindings start incoming checked canonical left right
  | publication {start incoming labels left right tree}
      (paths : PairedPublicationWriterPrefix profile ready base bindings tree start incoming labels left right) :
      VisitorWriterPath profile ready base bindings start incoming labels labels left right
  | callbackBoundary {start incoming checked canonical left right}
      (boundary : CallbackWriterBoundary profile ready base bindings start incoming checked canonical left right)
      (paths : PairedWriterPaths profile ready base bindings start incoming checked canonical left right) :
      VisitorWriterPath profile ready base bindings start incoming checked canonical left right
  | append {start incoming checked canonical left right leftTail rightTail finish peer}
      (front : VisitorWriterPath profile ready base bindings start incoming checked canonical left right)
      (tail : VisitorWriterPath profile ready base bindings left right leftTail rightTail finish peer) :
      VisitorWriterPath profile ready base bindings start incoming (checked ++ leftTail) (canonical ++ rightTail) finish peer

open Stored.OwnedMemory.Claims in
/-- Ordered classified writer effects before a conflict or open assignment.
The spend list records checked-only compiled guard commits. Shared scheduled
commits and publications retain their own evidence and add no one-sided spend. -/
inductive ClassifiedWriterPrefix (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig)) :
    Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
    Trace grow sig → Trace grow sig → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
    List Spend → Prop where
  | framed {start incoming checked canonical left right}
      (lhs : WriterPath profile ready (specDispatch ready base) start checked left [])
      (rhs : WriterPath profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming canonical right []) :
      ClassifiedWriterPrefix profile ready base bindings start incoming checked canonical left right []
  | spend {start incoming checked canonical left right change update}
      (source : CompiledLeafSource start (some update))
      (commit : ReachedLeafSpend profile ready (specDispatch ready base) start checked left change update)
      (raw : WriterPath profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming canonical right []) :
      ClassifiedWriterPrefix profile ready base bindings start incoming checked canonical left right [update]
  | recordEndpointCommit {start incoming left right site cx index ptr checkedNext canonicalNext}
      (lhs : ExecutedSharedRecordEndpointSpend profile ready (specDispatch ready base) site cx index ptr checkedNext start left)
      (rhs : ExecutedSharedRecordEndpointSpend profile ready (specDispatch ready (LiveDispatch.host bindings base))
        site cx index ptr canonicalNext incoming right) :
      ClassifiedWriterPrefix profile ready base bindings start incoming [.tau, .tau, .tau, .tau] [.tau, .tau, .tau, .tau] left right []
  | recordOwnerCommit {start incoming left right receipt cx index ptr rep checkedNext canonicalNext}
      (lhs : ExecutedSharedRecordOwnerSpend profile ready (specDispatch ready base) receipt cx index ptr rep checkedNext start left)
      (rhs : ExecutedSharedRecordOwnerSpend profile ready (specDispatch ready (LiveDispatch.host bindings base))
        receipt cx index ptr rep canonicalNext incoming right) :
      ClassifiedWriterPrefix profile ready base bindings start incoming [.tau, .tau, .tau] [.tau, .tau, .tau] left right []
  | ownerCommit {start incoming left right site rep leftTicket rightTicket}
      (lhs : ExecutedSharedOwnerSpend profile ready (specDispatch ready base) site rep leftTicket start left)
      (rhs : ExecutedSharedOwnerSpend profile ready (specDispatch ready (LiveDispatch.host bindings base)) site rep rightTicket incoming right) :
      ClassifiedWriterPrefix profile ready base bindings start incoming [.tau, .tau, .tau] [.tau, .tau, .tau] left right []
  | dropCommit {start incoming left right site rep leftTicket rightTicket result preparation}
      (lhs : ExecutedSharedDropSpend profile ready (specDispatch ready base) site rep leftTicket result preparation start left)
      (rhs : ExecutedSharedDropSpend profile ready (specDispatch ready (LiveDispatch.host bindings base))
        site rep rightTicket result preparation incoming right) :
      ClassifiedWriterPrefix profile ready base bindings start incoming
        (.tau :: (preparation ++ [.tau, .tau])) (.tau :: (preparation ++ [.tau, .tau])) left right []
  | endpointCommit {start incoming left right site leftTicket rightTicket}
      (lhs : ExecutedSharedEndpointSpend profile ready (specDispatch ready base) site leftTicket start left)
      (rhs : ExecutedSharedEndpointSpend profile ready (specDispatch ready (LiveDispatch.host bindings base)) site rightTicket incoming right) :
      ClassifiedWriterPrefix profile ready base bindings start incoming [.tau, .tau, .tau, .tau] [.tau, .tau, .tau, .tau] left right []
  | copyTransfer {start incoming left right check canon endpoint buffer reading action next}
      (lhs : ExecutedCopyTransfer profile ready (specDispatch ready base) check endpoint buffer reading action next start left)
      (rhs : ExecutedCopyTransfer profile ready (specDispatch ready (LiveDispatch.host bindings base))
        canon endpoint buffer reading action next incoming right) :
      ClassifiedWriterPrefix profile ready base bindings start incoming [.tau, .tau] [.tau, .tau] left right []
  | publication {start incoming labels left right tree}
      (paths : PairedPublicationWriterPrefix profile ready base bindings tree start incoming labels left right) :
      ClassifiedWriterPrefix profile ready base bindings start incoming labels labels left right []
  | append {start incoming checked canonical left right leftTail rightTail finish peer first second}
      (front : ClassifiedWriterPrefix profile ready base bindings start incoming checked canonical left right first)
      (tail : ClassifiedWriterPrefix profile ready base bindings left right leftTail rightTail finish peer second) :
      ClassifiedWriterPrefix profile ready base bindings start incoming (checked ++ leftTail) (canonical ++ rightTail)
        finish peer (first ++ second)

open ReturnFrame.Occurrence in
/-- Each active or saved occurrence follows the actual prefix to the
hostGet, then stays at its reached location through that read. -/
def ReachedReadOccurrences (profile : ProfileKind) (ready : HostReady (HostState sig))
    (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (start reader after : Config (core3 grow) (HostState sig)) (leading : Trace grow sig) : Prop :=
  ∀ place, ∃ reached, Trail profile ready dispatch start place leading reader reached ∧
    Trail profile ready dispatch reader reached [.tau] after reached

open Stored.OwnedMemory.Claims.Record in
/-- Interpret the reached writer sites up to the first conflicting read
or missing source classification. The remaining paths are retained, not replayed. -/
inductive WriterDiscrepancyCut (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (start incoming : Config (core3 grow) (HostState sig)) (pending : Stored.OwnedMemory.Claims.Spend → Prop) :
    Trace grow sig → Trace grow sig → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) → Prop where
  | complete {checked canonical left right} (spends : List Stored.OwnedMemory.Claims.Spend)
      (certified : ClassifiedWriterPrefix profile ready base bindings start incoming checked canonical left right spends)
      (related : left.host.writer.ClaimDiscrepancies right.host.writer (fun probe => pending probe ∨ probe ∈ spends)) :
      WriterDiscrepancyCut profile ready base bindings start incoming pending checked canonical left right
  | prepareConflict {checked canonical left right atLeft atRight reader leading rawLeading readLeft readRight tailChecked tailCanonical plan probe}
      (spends : List Stored.OwnedMemory.Claims.Spend)
      (front : VisitorWriterPath profile ready base bindings start incoming checked canonical atLeft atRight)
      (certified : ClassifiedWriterPrefix profile ready base bindings start incoming checked canonical atLeft atRight spends)
      (related : atLeft.host.writer.ClaimDiscrepancies atRight.host.writer (fun demand => pending demand ∨ demand ∈ spends))
      (site : ExecutedPrepareRead profile ready base atLeft reader readLeft readRight leading plan)
      (lhs : WriterPath profile ready (specDispatch ready base) atLeft (leading ++ [.tau]) readLeft [])
      (rhs : WriterPath profile ready (specDispatch ready (LiveDispatch.host bindings base)) atRight rawLeading readRight [])
      (checkedRead : ReachedReadOccurrences profile ready (specDispatch ready base)
        start reader readLeft (checked ++ leading))
      (rawTrail : ∀ place, ∃ reached, ReturnFrame.Occurrence.Trail profile ready
        (specDispatch ready (LiveDispatch.host bindings base)) incoming place (canonical ++ rawLeading) readRight reached)
      (live : pending probe ∨ probe ∈ spends)
      (unequal : prepare reader.store reader.host.writer plan ≠ prepare reader.store readRight.host.writer plan)
      (conflict : ReachedPrepareConflict reader.store reader.host.writer readRight.host.writer plan probe)
      (tail : VisitorWriterPath profile ready base bindings readLeft readRight tailChecked tailCanonical left right) :
      WriterDiscrepancyCut profile ready base bindings start incoming pending
        (checked ++ (leading ++ [.tau]) ++ tailChecked) (canonical ++ rawLeading ++ tailCanonical) left right
  | registrationConflict {checked canonical left right atLeft atRight readLeft readRight tailChecked tailCanonical
      check canon leftTicket rightTicket caller tree}
      (spends : List Stored.OwnedMemory.Claims.Spend)
      (front : VisitorWriterPath profile ready base bindings start incoming checked canonical atLeft atRight)
      (certified : ClassifiedWriterPrefix profile ready base bindings start incoming checked canonical atLeft atRight spends)
      (site : RegistrationProbeMismatch atLeft atRight readLeft readRight check canon leftTicket rightTicket caller tree)
      (lhs : WriterPath profile ready (specDispatch ready base) atLeft [.tau] readLeft [])
      (rhs : WriterPath profile ready (specDispatch ready (LiveDispatch.host bindings base)) atRight [.tau] readRight [])
      (checkedRead : ReachedReadOccurrences profile ready (specDispatch ready base) start atLeft readLeft checked)
      (rawRead : ReachedReadOccurrences profile ready (specDispatch ready (LiveDispatch.host bindings base))
        incoming atRight readRight canonical)
      (related : readLeft.host.writer.ClaimDiscrepancies readRight.host.writer (fun demand => pending demand ∨ demand ∈ spends))
      (conflict : RegistrationConflict readLeft.host.writer readRight.host.writer tree (fun demand => pending demand ∨ demand ∈ spends))
      (tail : VisitorWriterPath profile ready base bindings readLeft readRight tailChecked tailCanonical left right) :
      WriterDiscrepancyCut profile ready base bindings start incoming pending
        (checked ++ [.tau] ++ tailChecked) (canonical ++ [.tau] ++ tailCanonical) left right
  | sharedGiveConflict {checked canonical left right atLeft atRight readLeft readRight tailChecked tailCanonical
      check canon leftTicket rightTicket inst claim}
      (spends : List Spend)
      (front : VisitorWriterPath profile ready base bindings start incoming checked canonical atLeft atRight)
      (certified : ClassifiedWriterPrefix profile ready base bindings start incoming checked canonical atLeft atRight spends)
      (site : SharedGiveProbeMismatch claim inst leftTicket rightTicket atLeft atRight readLeft readRight check canon)
      (lhs : WriterPath profile ready (specDispatch ready base) atLeft [.tau] readLeft [])
      (rhs : WriterPath profile ready (specDispatch ready (LiveDispatch.host bindings base)) atRight [.tau] readRight [])
      (checkedRead : ReachedReadOccurrences profile ready (specDispatch ready base) start atLeft readLeft checked)
      (rawRead : ReachedReadOccurrences profile ready (specDispatch ready (LiveDispatch.host bindings base))
        incoming atRight readRight canonical)
      (related : readLeft.host.writer.ClaimDiscrepancies readRight.host.writer (fun demand => pending demand ∨ demand ∈ spends))
      (exceptional : pending claim.demand ∨ claim.demand ∈ spends)
      (different : ¬ claim.demand.ObservationAgrees readLeft.host.writer readRight.host.writer)
      (tail : VisitorWriterPath profile ready base bindings readLeft readRight tailChecked tailCanonical left right) :
      WriterDiscrepancyCut profile ready base bindings start incoming pending
        (checked ++ [.tau] ++ tailChecked) (canonical ++ [.tau] ++ tailCanonical) left right
  | sharedRecordConflict {checked canonical left right atLeft atRight readLeft readRight tailChecked tailCanonical
      check canon plan probe}
      (spends : List Spend)
      (front : VisitorWriterPath profile ready base bindings start incoming checked canonical atLeft atRight)
      (certified : ClassifiedWriterPrefix profile ready base bindings start incoming checked canonical atLeft atRight spends)
      (site : SharedRecordPrepareMismatch atLeft atRight readLeft readRight plan check canon)
      (lhs : WriterPath profile ready (specDispatch ready base) atLeft [.tau] readLeft [])
      (rhs : WriterPath profile ready (specDispatch ready (LiveDispatch.host bindings base)) atRight [.tau] readRight [])
      (checkedRead : ReachedReadOccurrences profile ready (specDispatch ready base) start atLeft readLeft checked)
      (rawRead : ReachedReadOccurrences profile ready (specDispatch ready (LiveDispatch.host bindings base))
        incoming atRight readRight canonical)
      (related : atLeft.host.writer.ClaimDiscrepancies atRight.host.writer (fun demand => pending demand ∨ demand ∈ spends))
      (live : pending probe ∨ probe ∈ spends)
      (conflict : ReachedPrepareConflict atLeft.store atLeft.host.writer atRight.host.writer plan probe)
      (tail : VisitorWriterPath profile ready base bindings readLeft readRight tailChecked tailCanonical left right) :
      WriterDiscrepancyCut profile ready base bindings start incoming pending
        (checked ++ [.tau] ++ tailChecked) (canonical ++ [.tau] ++ tailCanonical) left right
  | recordOwnerConflict {checked canonical left right atLeft atRight readLeft readRight tailChecked tailCanonical
      receipt cx index ptr check canon}
      (spends : List Spend)
      (front : VisitorWriterPath profile ready base bindings start incoming checked canonical atLeft atRight)
      (certified : ClassifiedWriterPrefix profile ready base bindings start incoming checked canonical atLeft atRight spends)
      (site : SharedRecordOwnerProbeMismatch atLeft atRight readLeft readRight receipt cx index ptr check canon)
      (lhs : WriterPath profile ready (specDispatch ready base) atLeft [.tau] readLeft [])
      (rhs : WriterPath profile ready (specDispatch ready (LiveDispatch.host bindings base)) atRight [.tau] readRight [])
      (checkedRead : ReachedReadOccurrences profile ready (specDispatch ready base) start atLeft readLeft checked)
      (rawRead : ReachedReadOccurrences profile ready (specDispatch ready (LiveDispatch.host bindings base))
        incoming atRight readRight canonical)
      (related : atLeft.host.writer.ClaimDiscrepancies atRight.host.writer (fun demand => pending demand ∨ demand ∈ spends))
      (exceptional : pending (.owner (receiptId receipt)) ∨ .owner (receiptId receipt) ∈ spends)
      (different : ¬ (Spend.owner (receiptId receipt)).ObservationAgrees atLeft.host.writer atRight.host.writer)
      (tail : VisitorWriterPath profile ready base bindings readLeft readRight tailChecked tailCanonical left right) :
      WriterDiscrepancyCut profile ready base bindings start incoming pending
        (checked ++ [.tau] ++ tailChecked) (canonical ++ [.tau] ++ tailCanonical) left right
  | recordEndpointConflict {checked canonical left right atLeft atRight readLeft readRight tailChecked tailCanonical site}
      (spends : List Spend)
      (front : VisitorWriterPath profile ready base bindings start incoming checked canonical atLeft atRight)
      (certified : ClassifiedWriterPrefix profile ready base bindings start incoming checked canonical atLeft atRight spends)
      (mismatch : SharedRecordEndpointMismatch profile ready base bindings site atLeft atRight readLeft readRight)
      (checkedRead : ReachedReadOccurrences profile ready (specDispatch ready base)
        start mismatch.checkedRead readLeft (checked ++ [.tau]))
      (rawRead : ReachedReadOccurrences profile ready (specDispatch ready (LiveDispatch.host bindings base))
        incoming mismatch.canonicalRead readRight (canonical ++ [.tau]))
      (related : atLeft.host.writer.ClaimDiscrepancies atRight.host.writer (fun demand => pending demand ∨ demand ∈ spends))
      (exceptional : pending (.endpoint site.identity) ∨ .endpoint site.identity ∈ spends)
      (different : ¬ (Spend.endpoint site.identity).ObservationAgrees atLeft.host.writer atRight.host.writer)
      (tail : VisitorWriterPath profile ready base bindings readLeft readRight tailChecked tailCanonical left right) :
      WriterDiscrepancyCut profile ready base bindings start incoming pending
        (checked ++ [.tau, .tau] ++ tailChecked) (canonical ++ [.tau, .tau] ++ tailCanonical) left right
  | boundary {checked canonical left right atLeft atRight siteChecked siteCanonical siteLeft siteRight tailChecked tailCanonical}
      (spends : List Stored.OwnedMemory.Claims.Spend)
      (front : VisitorWriterPath profile ready base bindings start incoming checked canonical atLeft atRight)
      (certified : ClassifiedWriterPrefix profile ready base bindings start incoming checked canonical atLeft atRight spends)
      (related : atLeft.host.writer.ClaimDiscrepancies atRight.host.writer (fun probe => pending probe ∨ probe ∈ spends))
      (site : CallbackWriterBoundary profile ready base bindings atLeft atRight siteChecked siteCanonical siteLeft siteRight)
      (actual : PairedWriterPaths profile ready base bindings atLeft atRight siteChecked siteCanonical siteLeft siteRight)
      (tail : VisitorWriterPath profile ready base bindings siteLeft siteRight tailChecked tailCanonical left right) :
      WriterDiscrepancyCut profile ready base bindings start incoming pending
        (checked ++ siteChecked ++ tailChecked) (canonical ++ siteCanonical ++ tailCanonical) left right

/-- Reached allocator steps before a protected return. Ordinary steps must
not install an overlaid give or assign the host; confined gives and
reached host reads with a closed observation have their own rules. The endpoint may
be suspended, trapped, ready to pop a protected frame, or at an open hook. -/
inductive ClosedCallbackPrefix (bindings : List (Binding sig)) (profile : ProfileKind)
    (ready : HostReady (HostState sig)) (base : HostImpl (core3 grow) (HostState sig))
    (protectedReturn : ReturnFrame.Continuation (core3 grow) (HostState sig) → Prop) :
    Config (core3 grow) (HostState sig) → Trace grow sig → Config (core3 grow) (HostState sig) → Prop where
  | done (state : Config (core3 grow) (HostState sig)) : ClosedCallbackPrefix bindings profile ready base protectedReturn state [] state
  | step {start next finish label seen}
      (interior : HostFrame.InteriorFor protectedReturn start) (unchanged : UnchangedAt bindings start)
      (noAssignment : NoHostAssignment start) (grows : CoreUpdateGrows start)
      (run : Step profile ready (specDispatch ready base) start label next)
      (tail : ClosedCallbackPrefix bindings profile ready base protectedReturn next seen finish) :
      ClosedCallbackPrefix bindings profile ready base protectedReturn start (PayloadPrefix.visible [label] ++ seen) finish
  | confinedGive {start finish seen} (callout : LinkedCallback.ClosedGive bindings start)
      (tail : ClosedCallbackPrefix bindings profile ready base protectedReturn callout.resume seen finish) :
      ClosedCallbackPrefix bindings profile ready base protectedReturn start seen finish
  | closedRead {start finish seen thread frames rest resume}
      (focused : start.ctl = ⟨thread, .prog (.op .hostGet resume), frames⟩ :: rest)
      (agrees : ∀ host, resume start.host = resume host)
      (tail : ClosedCallbackPrefix bindings profile ready base protectedReturn { start with ctl := ⟨thread,
        .prog (resume start.host), frames⟩ :: rest } seen finish) :
      ClosedCallbackPrefix bindings profile ready base protectedReturn start seen finish

/-- A reached synchronous lift read whose candidate filter is independent
of the embedder host at the consulted queries. -/
def ClosedSyncReadyRead (ready : HostReady (HostState sig)) (state : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ task inst thread frames rest,
    state.ctl = ⟨thread, .prog (.op .hostGet (fun current =>
      syncLiftCandidates task (state.store.instCandidates (ready current) inst))), frames⟩ :: rest ∧
    LinkedCallback.ReadyAgreement ready state inst

/-- The actual reached read produces the same continuation for any host journal. This makes
no assertion about future reads or the existence of a runnable thread. -/
def ClosedHostRead (state : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ thread resume frames rest,
    state.ctl = ⟨thread, .prog (.op .hostGet resume), frames⟩ :: rest ∧
    ∀ host, resume state.host = resume host

/-- Parameters obtained from the reached callout checks and live handle lookup. -/
structure WaitableCalloutEntry where
  inst : InstId
  set : WsetId
  ptr : Nat

/-- Shared by the early and actually resumed wait. Selection reads the
current store at this point, not the event checked by the readiness read. -/
def waitableWaitContinue (mem : (core3 grow).MemAddr) (entry : WaitableCalloutEntry) : Session grow sig (Ret (core3 grow)) := do
  modifyStore (CStore.wsetDecWaitingSt entry.set)
  let event ← wsetGetPendingEvent entry.set
  let code ← unpackEvent (Builtins.eventCx mem entry.inst) entry.ptr event
  pure (.flat [i32Flat code])

/-- The continuation after the optional synchronous cancellation wait.
Release the current sync waiter and recheck the current resolution. -/
def cancelFinish (subtask : SubtaskId) : Session grow sig (Ret (core3 grow)) := do
  modifyStore (CStore.setSyncWaiterSt (.subtask subtask) none)
  if ← Builtins.subtaskResolvedNow subtask then
    return .flat (← Builtins.subtaskCancelDeliver subtask)
  else return .flat [i32Flat (AsyncRef.subtaskCancelResult none)]

/-- The actual legacy accept import determines the synchronous loader and
its instance. Both loaders consult the accepted history for child indices. -/
inductive LinkedCoreAcceptLoader (bindings : List (Binding sig)) (name : String)
    (kind : Silmaril.Wasm.V1.FuncType) (args : List FlatValue) :
    InstId → (World grow sig → CStore (core3 grow) × Except Core.Issue (Stored.OwnedMemory.Tree sig)) → Prop where
  | memory (contract : Stored.Endpoints.Core.Contract sig) (memory : Option Nat)
      (linked : resolveBinding bindings name kind = .ok ⟨name, contract.inst, .accept contract memory⟩) :
      LinkedCoreAcceptLoader bindings name kind args contract.inst
        (fun state => Core.load contract memory state (Stored.Endpoints.Core.Scheduled.nodeCall contract state.reference args))
  | flat (source : FlatSource sig)
      (linked : resolveBinding bindings name kind = .ok ⟨name, source.inst, .acceptFlat source⟩) :
      LinkedCoreAcceptLoader bindings name kind args source.inst (fun state => source.load state args)

section LegacyChildHistory

open Silmaril.Wasm.Game (UCall)
open Silmaril.Wasm.Game.Accept (Callout)
open Silmaril.Wasm.Game.HandleAccept.Memory (le32s)
open Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst (checkNodeMode checkedCallout nodeOperands)
open Stored.Endpoints.Core (childFromHistory checkChildren Contract)

/-- The first differing child lookup after a shared successful prefix of the
handle words actually decoded by the loader. -/
inductive VisitedChildMismatch {Value : Type} (left right : List Value) : List (BitVec 32) → Prop where
  | first {handle tail} (different : childFromHistory left handle ≠ childFromHistory right handle) :
      VisitedChildMismatch left right (handle :: tail)
  | next {handle tail child} (checked : childFromHistory left handle = some child)
      (canonical : childFromHistory right handle = some child) (later : VisitedChildMismatch left right tail) :
      VisitedChildMismatch left right (handle :: tail)

/-- The history demand made by two already admitted loaders. -/
inductive ChildHistoryDemand {sig : Signature} {Value : Type}
    (left right : List Value) (tag : sig.Tag) (observed : Callout) (pointer count : Nat)
    (beforeLookup : Prop) : Prop where
  | capacity (different : checkChildren sig tag left.length pointer count ≠
      checkChildren sig tag right.length pointer count) : ChildHistoryDemand left right tag observed pointer count beforeLookup
  | child {bytes handles} (admitted : beforeLookup)
      (checked : checkChildren sig tag left.length pointer count = .ok ())
      (canonical : checkChildren sig tag right.length pointer count = .ok ())
      (range : observed.segment pointer (4 * count) = some bytes) (decoded : le32s bytes = some handles)
      (different : VisitedChildMismatch left right handles) : ChildHistoryDemand left right tag observed pointer count beforeLookup

/-- History demand after the shared executable memory preflight inputs check. -/
def LegacyMemoryChildDemand {Value : Type} (contract : Contract sig)
    (check : Stored.TypeOf → Except Stored.Issue Unit) (memory : Option Nat)
    (left right : List Value) (call : UCall Nat) : Prop :=
  ∃ mem observed rawTag payload pointer count tag,
    checkNodeMode contract.mode = .ok () ∧ memory = some mem ∧
    checkedCallout contract.name mem call contract.mode.address = .ok observed ∧
    nodeOperands contract.mode.address observed.args = some (rawTag, payload, pointer, count) ∧
    contract.tagOf rawTag = some tag ∧ check (sig.payload tag) = .ok () ∧
    ChildHistoryDemand left right tag observed pointer count
      (let layout := ABI.layout contract.mode.address (sig.payload tag)
       payload % layout.alignment.bytes = 0 ∧ ∃ bytes, observed.segment payload layout.size = some bytes)

/-- History demand after the shared executable flat preflight inputs check. -/
def LegacyFlatChildDemand (source : FlatSource sig) (store : CStore (core3 grow))
    (left right : Stored.OwnedMemory.Claims.State sig) (args : List FlatValue) : Prop :=
  ∃ observed pointer count payload,
    Core.checkFlatSchema (sig.payload source.tag) = .ok () ∧
    checkedCallout source.name source.memory ⟨0, { mems := store.core.mems }, []⟩ source.width = .ok observed ∧
    args = pointer :: count :: payload ∧
    (Stored.flatType pointer != ABI.pointerType source.width || Stored.flatType count != ABI.pointerType source.width) = false ∧
    (payload.map Stored.flatType != ABI.flatten source.width (sig.payload source.tag)) = false ∧
    ChildHistoryDemand left.accepted right.accepted source.tag observed (flatNat pointer) (flatNat count) True

/-- History evidence at a linked source loader whose two reads use the same
reached canonical store. No lookup in this certificate confers nominal authority. -/
inductive LinkedCoreAcceptHistoryDemand (bindings : List (Binding sig)) (name : String)
    (kind : Silmaril.Wasm.V1.FuncType) (args : List FlatValue) (left right : World grow sig) :
    InstId → (World grow sig → CStore (core3 grow) × Except Core.Issue (Stored.OwnedMemory.Tree sig)) → Prop where
  | memory (contract : Contract sig) (memory : Option Nat)
      (linked : resolveBinding bindings name kind = .ok ⟨name, contract.inst, .accept contract memory⟩)
      (stores : left.reference = right.reference)
      (demand : LegacyMemoryChildDemand contract Stored.OwnedMemory.checkSchema memory left.writer.accepted
        right.writer.accepted (Stored.Endpoints.Core.Scheduled.nodeCall contract left.reference args)) :
      LinkedCoreAcceptHistoryDemand bindings name kind args left right contract.inst
        (fun state => Core.load contract memory state (Stored.Endpoints.Core.Scheduled.nodeCall contract state.reference args))
  | flat (source : FlatSource sig)
      (linked : resolveBinding bindings name kind = .ok ⟨name, source.inst, .acceptFlat source⟩)
      (stores : left.reference = right.reference)
      (demand : LegacyFlatChildDemand source left.reference left.writer right.writer args) :
      LinkedCoreAcceptHistoryDemand bindings name kind args left right source.inst (fun state => source.load state args)

end LegacyChildHistory

/-- A resolved legacy action can carry an instance different from the
binding's instance. The executable handler returns a typed context error. -/
def LegacyBindingContextMismatch (binding : Binding sig) : Prop :=
  match binding.action with
  | .accept contract _ => contract.inst ≠ binding.inst
  | .acceptFlat source => source.inst ≠ binding.inst
  | _ => False

/-- Both kinds of resolved legacy accept entry selected by the source fold. -/
def LinkedLegacyAccept (bindings : List (Binding sig)) (name : String)
    (kind : Silmaril.Wasm.V1.FuncType) (args : List FlatValue) : Prop :=
  (∃ inst loader, LinkedCoreAcceptLoader (grow := grow) bindings name kind args inst loader) ∨
    ∃ binding, resolveBinding bindings name kind = .ok binding ∧ LegacyBindingContextMismatch binding

/-- The linked callout can be installed by a parked Core caller or by an
executed program call. The two instructions push different continuations. -/
inductive LegacyAcceptCallAt (before : Config (core3 grow) (HostState sig))
    (name : String) (kind : Silmaril.Wasm.V1.FuncType) (args : List FlatValue) : Prop where
  | core {thread core resume frames rest}
      (focus : before.ctl = ⟨thread, .core core resume, frames⟩ :: rest)
      (calling : (core3 grow).status before.store.core core = .callout (.embedder name kind) args)
  | program {thread resume frames rest}
      (focus : before.ctl = ⟨thread, .prog (.op (.call (.hostCallout (.embedder name kind) args)) resume), frames⟩ :: rest)

/-- A shared selector executed the accepted-history lookup on both sides and
selected different roots at the demanded index. -/
structure SharedGiveHistoryMismatch (action : SharedGiveAction) (inst : InstId) (leftTicket rightTicket position : Nat)
    (handle : BitVec IntType.i32.width)
    (beforeLeft beforeRight left right : Config (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) : Prop where
  leftRead : beforeLeft.ctl = check.control (select handle >>= action.afterLookup inst leftTicket position)
  rightRead : beforeRight.ctl = canon.control (select handle >>= action.afterLookup inst rightTicket position)
  leftReached : left = { beforeLeft with ctl := check.control (action.afterLookup inst leftTicket position
    (Stored.Endpoints.Core.childFromHistory beforeLeft.host.writer.accepted handle)) }
  rightReached : right = { beforeRight with ctl := canon.control (action.afterLookup inst rightTicket position
    (Stored.Endpoints.Core.childFromHistory beforeRight.host.writer.accepted handle)) }
  different : Stored.Endpoints.Core.childFromHistory beforeLeft.host.writer.accepted handle ≠
    Stored.Endpoints.Core.childFromHistory beforeRight.host.writer.accepted handle

/-- The host frame left to run after the thread selected by Store.tick
returns to its resumer. -/
def sourceTickReturn : Session grow sig (Ret (core3 grow)) := do
  modifyStore StepDefs.leaveHostSt
  pure .unit

/-- The executable tick choice followed by the selected thread's resume and
the host return. The empty candidate list goes straight to the host return. -/
def sourceTickCandidates (candidates : List ThreadId) : Session grow sig (Ret (core3 grow)) :=
  match candidates with
  | [] => sourceTickReturn
  | first :: rest => pickTick first rest >>= fun selected => Thread.resume selected >>= fun _ => sourceTickReturn

/-- The actual readiness read after tick has entered the host and captured
the store. -/
def sourceTickRead (ready : HostReady (HostState sig)) (store : CStore (core3 grow)) :
    Session grow sig (Ret (core3 grow)) :=
  .op .hostGet fun host => sourceTickCandidates (store.candidates (ready host))

/-- The two reached tick reads disagree on a blocked waiting thread's host
query. Both compute their ordered candidate lists from the shared store. -/
structure TickReadinessMismatch (ready : HostReady (HostState sig))
    (checked canonical : Config (core3 grow) (HostState sig)) where
  stores : checked.store = canonical.store
  thread : ThreadId
  entry : Thread
  query : Nat
  waiting : thread ∈ checked.store.waiting
  live : checked.store.thread? thread = some entry
  blocked : entry.blocked = true
  condition : entry.readyCond = some (.host query)
  different : ready checked.host query ≠ ready canonical.host query
  candidates : checked.store.candidates (ready checked.host) ≠ canonical.store.candidates (ready canonical.host)

/-- The first executed action not covered by the closed callback rules.
This is a proof cut, not a new runtime rejection. -/
inductive CallbackWorkerBoundary (bindings : List (Binding sig)) (ready : HostReady (HostState sig))
    (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (protectedReturn : ReturnFrame.Continuation (core3 grow) (HostState sig) → Prop)
    (before : Config (core3 grow) (HostState sig)) (label : Label (core3 grow) (HostState sig))
    (next : Config (core3 grow) (HostState sig)) : Prop where
  | give (install : GiveInstall bindings dispatch before label next)
  | coreAcceptInstall {name kind args}
      (call : LegacyAcceptCallAt before name kind args)
      (source : LinkedLegacyAccept (grow := grow) bindings name kind args)
  | sharedGiveInstall {name kind args inst} {action : SharedGiveAction}
      (call : LegacyAcceptCallAt before name kind args)
      (linked : resolveBinding bindings name kind = .ok ⟨name, inst, action.bindingAction⟩) :
      CallbackWorkerBoundary bindings ready dispatch protectedReturn before label next
  | componentInstall {active hostId caller resume frames rest}
      (focus : before.ctl = ⟨some active, .prog (.op (.call (.hostFunc hostId caller)) resume), frames⟩ :: rest)
  | pollInstall {thread core resume frames rest mem inst args}
      (focus : before.ctl = ⟨thread, .core core resume, frames⟩ :: rest)
      (calling : (core3 grow).status before.store.core core = .callout (.builtin (.waitableSetPoll mem) inst) args)
  | waitInstall {thread core resume frames rest mem inst args}
      (focus : before.ctl = ⟨thread, .core core resume, frames⟩ :: rest)
      (calling : (core3 grow).status before.store.core core = .callout (.builtin (.waitableSetWait mem) inst) args)
  | cancelInstall {thread core resume frames rest async inst args}
      (focus : before.ctl = ⟨thread, .core core resume, frames⟩ :: rest)
      (calling : (core3 grow).status before.store.core core = .callout (.builtin (.subtaskCancel async) inst) args)
  | waitResume {waiter resumer afterResume frames rest core resume savedFrames mem entry}
      (focus : before.ctl = ⟨resumer, .prog (.op (.resumeThread waiter) afterResume), frames⟩ :: rest)
      (found : before.cont? waiter = some ⟨some waiter, .prog (waitableWaitContinue mem entry), .core core resume :: savedFrames⟩)
  | cancelResume {waiter resumer afterResume frames rest core resume savedFrames subtask}
      (focus : before.ctl = ⟨resumer, .prog (.op (.resumeThread waiter) afterResume), frames⟩ :: rest)
      (found : before.cont? waiter = some ⟨some waiter, .prog (cancelFinish subtask), .core core resume :: savedFrames⟩)
  | tickResume {worker saved}
      (focus : before.ctl = [⟨none, .prog (.op (.resumeThread worker) (fun _ => sourceTickReturn)), []⟩])
      (found : before.cont? worker = some saved)
  | read {thread resume frames rest}
      (focus : before.ctl = ⟨thread, .prog (.op .hostGet resume), frames⟩ :: rest)
      (openRead : ¬ ClosedHostRead before)
  | protectedPop {thread value resume frames rest} (retained : protectedReturn resume)
      (focus : before.ctl = ⟨thread, .prog (.pure value), .prog resume :: frames⟩ :: rest)
  | write {thread value resume frames rest}
      (focus : before.ctl = ⟨thread, .prog (.op (.hostSet value) resume), frames⟩ :: rest)
  | nonGrowingUpdate (failed : ¬ CoreUpdateGrows before)

/-- Every initial occurrence follows the same reached coordinate on both
paths, even if checked journal steps add silent labels. This includes saved
locations and records loss without assuming later return. -/
def CoupledOccurrencePaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (checkEntry canonEntry : Config (core3 grow) (HostState sig)) (checkTrace canonTrace : Trace grow sig)
    (checked canonical : Config (core3 grow) (HostState sig)) : Prop :=
  open ReturnFrame.Occurrence in
  ∀ cursor : Option Location, ∃ reached,
    Trail profile ready (specDispatch ready base) checkEntry cursor checkTrace checked reached ∧
    Trail profile ready (specDispatch ready (LiveDispatch.host bindings base)) canonEntry cursor canonTrace canonical reached

/-- The same occurrence map both witnesses the machine paths and transports
the older relation around every enclosing mark. In particular a fresh
frame cannot take the place of a lost occurrence. -/
def OccurrenceTransport (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (checkEntry canonEntry : Config (core3 grow) (HostState sig)) (checkTrace canonTrace : Trace grow sig)
    (checked canonical : Config (core3 grow) (HostState sig)) (introduced : List (Option ReturnFrame.Occurrence.Location) := []) : Prop :=
  open ReturnFrame.Occurrence in
  ∃ move : Option Location → Option Location,
    (∀ cursor, Trail profile ready (specDispatch ready base) checkEntry cursor checkTrace checked (move cursor) ∧
      Trail profile ready (specDispatch ready (LiveDispatch.host bindings base)) canonEntry cursor canonTrace canonical (move cursor)) ∧
    ∀ older marks, OutsideMarks older (segmentStorage checkEntry) (segmentStorage canonEntry) marks →
      OutsideMarks older (segmentStorage checked) (segmentStorage canonical) (introduced ++ marks.map move)

/-- Compare the scheduler and all enclosing continuations while the focused
component programs carry distinct diagnostic data. Normalizing the focus is
only a relation on configurations, not a machine transition. -/
def PairedComponentSite (changes : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (left right : Config (core3 grow) (HostState sig))
    (leftCursor rightCursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) : Prop :=
  HostFrame.Related.Paired changes
    { left with ctl := leftCursor.control (.pure (.cancel .none)) }
    { right with ctl := rightCursor.control (.pure (.cancel .none)) }

/-- The operations that can be compared using just the reached shared store
and active thread, without consulting either embedder. -/
def componentStoreOp : (Eff (core3 grow) (HostState sig)).Op → Bool
  | .get | .modify _ | .currentThread | .choose _ | .trap _ => true
  | _ => false

def waitableCalloutHost (poll : Bool) (mem : (core3 grow).MemAddr) (inst : InstId) : CanonHost (core3 grow) :=
  .builtin (if poll then .waitableSetPoll mem else .waitableSetWait mem) inst

/-- The shared entry of the public poll and wait programs, before either can
select an event or change the waiter's count. -/
def waitableCalloutEntry (poll : Bool) (mem : (core3 grow).MemAddr) (inst : InstId) (args : List FlatValue) :
    Session grow sig WaitableCalloutEntry := do
  let thread ← currentThread
  let store ← getStore
  match calloutEntry store thread (waitableCalloutHost poll mem inst) with
  | some reason => trap reason
  | none => withArgs2 args fun index ptr => do
    let current ← Builtins.enterWaitableBuiltin
    let set ← Builtins.expectWset (← handlesGet current index)
    pure ⟨current, set, ptr⟩

def waitableCalloutBody (poll : Bool) (mem : (core3 grow).MemAddr) (entry : WaitableCalloutEntry) :
    Session grow sig (Ret (core3 grow)) := do
  let event ← if poll then wsetPoll entry.set else wsetWait entry.set
  let code ← unpackEvent (Builtins.eventCx mem entry.inst) entry.ptr event
  pure (.flat [i32Flat code])

/-- Checked entry of public cancellation before the request write or event
take. A resolved subtask requires no hook; an unresolved one retains the
reached cancellation reference, including a no-op hook. -/
def cancelCalloutEntry (async : Bool) (inst : InstId) (args : List FlatValue) :
    Session grow sig (SubtaskId × Option CancelRef) := do
  let thread ← currentThread
  let store ← getStore
  match calloutEntry store thread (.builtin (.subtaskCancel async) inst) with
  | some reason => trap reason
  | none => withArgs1 args fun index => do
    let current ← Builtins.enterWaitableBuiltin
    let subtask ← Builtins.expectSubtask (← handlesGet current index)
    trapIf (← Subtask.resolveDelivered subtask) .subtaskCancelTwice
    let record ← getObj ArenaField.subtasks subtask
    trapIf record.cancellationRequested .subtaskCancelTwice
    trapIf (← Runtime.Waitable.inWaitableSet (.subtask subtask)) .subtaskInSet
    pure (subtask, if record.state.resolved then none else some record.onCancel)

def cancelCalloutBody (async : Bool) (entry : SubtaskId × Option CancelRef) : Session grow sig (Ret (core3 grow)) := do
  let (subtask, hook) := entry
  match hook with
  | none => return .flat (← Builtins.subtaskCancelDeliver subtask)
  | some hook =>
    if ← Builtins.subtaskCancelRequest async subtask hook then
      return .flat (← Builtins.subtaskCancelDeliver subtask)
    else return .flat [i32Flat (AsyncRef.subtaskCancelResult none)]

def cancelRequestWrite (subtask : SubtaskId) : Session grow sig Unit := do
  let thread ← currentThreadId
  modifyStore (Builtins.WaitableSt.requestCancel subtask thread)

def cancelHookReturn (async : Bool) (subtask : SubtaskId) (result : Ret (core3 grow)) : Session grow sig (Ret (core3 grow)) := do
  let unitResult : Session grow sig Unit := match result with
    | .unit => pure ()
    | _ => internal "late-bound call: expected Ret.unit"
  unitResult
  Builtins.subtaskCancelSyncWait async subtask
  modifyStore (CStore.setSyncWaiterSt (.subtask subtask) none)
  if ← Builtins.subtaskResolvedNow subtask then
    return .flat (← Builtins.subtaskCancelDeliver subtask)
  else return .flat [i32Flat (AsyncRef.subtaskCancelResult none)]

def cancelAfterRequestWrite (async : Bool) (subtask : SubtaskId) (hook : CancelRef) : Session grow sig (Ret (core3 grow)) :=
  .op (.call (.onCancel hook)) (cancelHookReturn async subtask)

def cancelSyncDecision (async : Bool) (subtask : SubtaskId) : Session grow sig (Option ThreadId) := do
  let resolved ← Builtins.subtaskResolvedNow subtask
  if !async && !resolved then
    let thread ← currentThreadId
    let now ← Thread.readyNow (fun _ _ => false) (.subtaskResolved subtask)
    let early ← (if now then choose (.earlyReturn .syncSubtaskCancel) else pure false : Session grow sig Bool)
    if early then pure none else do
      Thread.startWaiting thread (.subtaskResolved subtask)
      pure (some thread)
  else pure none

/-- A hook return is not a public reply. Preserve the ordinary result-type
trap and, for a unit return, the executed async/sync readiness decision. -/
def cancelHookDecision (async : Bool) (subtask : SubtaskId) (result : Ret (core3 grow)) :
    Session grow sig (Option ThreadId) :=
  match result with
  | .unit => cancelSyncDecision async subtask
  | _ => internal "late-bound call: expected Ret.unit"

def cancelAfterHookDecision (subtask : SubtaskId) : Option ThreadId → Session grow sig (Ret (core3 grow))
  | none => cancelFinish subtask
  | some _ => block none >>= fun _ => cancelFinish subtask

/-- Cancellation consumes the currently reached event before reading the result state.
The event records what was delivered; only the result code is returned to Core. -/
def cancelDeliveryObservation (subtask : SubtaskId) : Session grow sig (AsyncRef.EventTuple × Nat) := do
  let event ← Runtime.Waitable.getPendingEvent (.subtask subtask)
  let record ← getObj ArenaField.subtasks subtask
  pure (event, AsyncRef.subtaskCancelResult (some record.state))

/-- Recheck at the reached finish, not at the hook install or wait decision.
Returning `[BLOCKED]` does not consume any pending event. -/
def cancelFinishObservation (subtask : SubtaskId) : Session grow sig (Option AsyncRef.EventTuple × Nat) := do
  modifyStore (CStore.setSyncWaiterSt (.subtask subtask) none)
  if ← Builtins.subtaskResolvedNow subtask then
    let (event, code) ← cancelDeliveryObservation subtask
    pure (some event, code)
  else pure (none, AsyncRef.subtaskCancelResult none)

/-- Record the event consumed by the public poll's actual buffer program.
Only the code becomes a flat result for Core. -/
def pollCalloutObservation (mem : (core3 grow).MemAddr) (inst : InstId) (args : List FlatValue) :
    Session grow sig (AsyncRef.EventTuple × Nat) := do
  let entry ← waitableCalloutEntry true mem inst args
  let event ← wsetPoll entry.set
  let code ← unpackEvent (Builtins.eventCx mem entry.inst) entry.ptr event
  pure (event, code)

def waitableFlatReply (observation : AsyncRef.EventTuple × Nat) : Session grow sig (Ret (core3 grow)) :=
  .pure (.flat [i32Flat observation.2])

/-- Run the actual waiter count update, readiness read and optional early
choice. A non-early answer commits the waiting record but has not blocked. -/
def waitableWaitDecision (entry : WaitableCalloutEntry) : Session grow sig (Option ThreadId) := do
  modifyStore (CStore.wsetIncWaitingSt entry.set)
  let thread ← currentThreadId
  let now ← Thread.readyNow (fun _ _ => false) (.wsetHasEvent entry.set)
  let early ← (if now then choose (.earlyReturn .waitableSetWait) else pure false : Session grow sig Bool)
  if early then pure none else do
    Thread.startWaiting thread (.wsetHasEvent entry.set)
    pure (some thread)

def waitableWaitAfterDecision (mem : (core3 grow).MemAddr) (entry : WaitableCalloutEntry) :
    Option ThreadId → Session grow sig (Ret (core3 grow))
  | none => waitableWaitContinue mem entry
  | some _ => block none >>= fun _ => waitableWaitContinue mem entry

/-- The frontier of an executed store-only component prefix. A pending
operation is not a refusal, and a trap does not run either continuation. -/
inductive ComponentStoreFrontier {Result : Type}
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (checkNext canonNext : Result → Session grow sig (Ret (core3 grow)))
    (left right : Config (core3 grow) (HostState sig)) (suffix : Trace grow sig)
    (closed : Prop := False) : Prop where
  | returned (result : Result)
      (checked : left.ctl = check.control (checkNext result))
      (canonical : right.ctl = canon.control (canonNext result))
      (paired : PairedComponentSite older left right check canon)
  | pending (op : (Eff (core3 grow) (HostState sig)).Op)
      (next : (Eff (core3 grow) (HostState sig)).Resp op → Session grow sig Result)
      (checked : left.ctl = check.control (.op op (fun response => next response >>= checkNext)))
      (canonical : right.ctl = canon.control (.op op (fun response => next response >>= canonNext)))
      (paired : PairedComponentSite older left right check canon)
      (boundary : suffix = [] ∨ (¬ closed ∧ componentStoreOp op = false))
  | trapped (checked : left.ctl = []) (canonical : right.ctl = [])
      (paired : HostFrame.Related.Paired older left right)

/-- The end of an actual finite flat-result callout cut. At reply focus the installed
caller is still live; only the rejoined case consumes its original slot. -/
inductive FlatCalloutExit {Observation : Type} (code : Observation → Nat)
    (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (left right : Config (core3 grow) (HostState sig)) (suffix : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop where
  | exhausted (noMore : suffix = []) (endpoint : finish = left)
  | trapped (checked : left.ctl = []) (canonical : right.ctl = []) (paired : HostFrame.Related.Paired older left right)
  | rejoined (observation : Observation) {thread core resume frames rest peerFrames peerRest remaining}
      (checked : left.ctl = ⟨thread, .prog (.pure (.flat [i32Flat (code observation)])), .core core resume :: frames⟩ :: rest)
      (canonical : right.ctl = ⟨thread, .prog (.pure (.flat [i32Flat (code observation)])), .core core resume :: peerFrames⟩ :: peerRest)
      (split : suffix = .tau :: remaining)
      (residual : Steps profile ready (specDispatch ready base)
        { left with ctl := ⟨thread, .core ((core3 grow).resume left.store.core core (.values [i32Flat (code observation)])) resume,
          frames⟩ :: rest } remaining finish)
      (paired : HostFrame.Related.Paired older
        { left with ctl := ⟨thread, .core ((core3 grow).resume left.store.core core (.values [i32Flat (code observation)])) resume,
          frames⟩ :: rest }
        { right with ctl := ⟨thread, .core ((core3 grow).resume right.store.core core (.values [i32Flat (code observation)])) resume,
          peerFrames⟩ :: peerRest })
      (writers : CheckedSpendFlow left.host.writer right.host.writer
        ({ left with ctl := ⟨thread, .core ((core3 grow).resume left.store.core core (.values [i32Flat (code observation)])) resume,
          frames⟩ :: rest } : Config (core3 grow) (HostState sig)).host.writer
        ({ right with ctl := ⟨thread, .core ((core3 grow).resume right.store.core core (.values [i32Flat (code observation)])) resume,
          peerFrames⟩ :: peerRest } : Config (core3 grow) (HostState sig)).host.writer [])
      (pop : OccurrenceTransport profile ready base bindings left right [.tau] [.tau]
        { left with ctl := ⟨thread, .core ((core3 grow).resume left.store.core core (.values [i32Flat (code observation)])) resume,
          frames⟩ :: rest }
        { right with ctl := ⟨thread, .core ((core3 grow).resume right.store.core core (.values [i32Flat (code observation)])) resume,
          peerFrames⟩ :: peerRest })

abbrev WaitableCalloutExit := FlatCalloutExit (grow := grow) (sig := sig) (Prod.snd : AsyncRef.EventTuple × Nat → Nat)

abbrev CancelFinishExit := FlatCalloutExit (grow := grow) (sig := sig) (Prod.snd : Option AsyncRef.EventTuple × Nat → Nat)

/-- The reached endpoint of a successful validation path. Publication can
reach the reply focus without returning to the caller or delivering an event. -/
inductive ComponentAcceptedFrontier
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (tree : Stored.OwnedMemory.Tree sig) (handle : Nat)
    (left right : Config (core3 grow) (HostState sig)) (suffix : Trace grow sig) : Prop where
  | pending (paired : PairedComponentSite older left right check canon) (exhausted : suffix = [])
  | trapped (checked : left.ctl = []) (canonical : right.ctl = [])
      (paired : HostFrame.Related.Paired older left right)
  | published (checked : left.ctl = check.control (.pure (.cancel .none)))
      (canonical : right.ctl = canon.control (.pure (.cancel .none)))
      (paired : HostFrame.Related.Paired older left right)
      (checkedLookup : Stored.Endpoints.Core.childFromHistory left.host.writer.accepted (BitVec.ofNat 32 handle) = some tree)
      (canonicalLookup : Stored.Endpoints.Core.childFromHistory right.host.writer.accepted (BitVec.ofNat 32 handle) = some tree)

/-- A finite input ending before a component protocol reaches its common
program. Both endpoints are at their original component cursors, with separate
focused programs and journals; the selected and enclosing occurrences follow
the actual consumed steps. -/
def ComponentEarlyPrefix (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (start incoming : Config (core3 grow) (HostState sig)) (labels : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig)) (limit : Nat) : Prop :=
  labels.length < limit ∧ ∃ peer,
    OccurrenceTransport profile ready base bindings start incoming labels labels finish peer ∧
    PairedComponentSite older finish peer check canon ∧
    (∃ program, finish.ctl = check.control program) ∧ (∃ program, peer.ctl = canon.control program)

/-- An interior component-entry cut with a frame at every executed writer site,
not just equal writers at the endpoints. -/
def FramedComponentEarlyPrefix (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (start incoming : Config (core3 grow) (HostState sig)) (labels : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig)) (limit : Nat) : Prop :=
  labels.length < limit ∧ ∃ peer,
    OccurrenceTransport profile ready base bindings start incoming labels labels finish peer ∧
    PairedComponentSite older finish peer check canon ∧
    VisitorWriterPath profile ready base bindings start incoming labels labels finish peer ∧
    (∃ program, finish.ctl = check.control program) ∧ (∃ program, peer.ctl = canon.control program)

def ComponentPublicationEarlyPrefix (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (tree : Stored.OwnedMemory.Tree sig) (start incoming : Config (core3 grow) (HostState sig))
    (labels : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  labels.length < 4 ∧ ∃ peer,
    OccurrenceTransport profile ready base bindings start incoming labels labels finish peer ∧
    PairedComponentSite older finish peer check canon ∧
    PairedPublicationWriterPrefix profile ready base bindings tree start incoming labels finish peer

/-- The reached host-frame refusal at a direct give. The canonical body has
no entry/completion journal steps; a checked prefix can end before the reply. -/
def DirectHostRefusalCut (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (name : String) (kind : V1.FuncType)
    (args : List FlatValue) (destination : RecordDestination) (schema : Option Stored.TypeOf)
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (entry peerEntry start incoming : Config (core3 grow) (HostState sig)) (labels : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig)) : Prop :=
  (labels.length < 6 ∧ PayloadPrefix.visible labels = [] ∧
    OccurrenceTransport profile ready base bindings entry peerEntry ([.tau, .tau, .tau] ++ labels) [.tau, .tau, .tau]
      finish incoming [some (.active 0 0)]) ∨
  ∃ trailing left right,
    let reply := giveAdmissionReply start.host.nextTicket destination schema .wrongContext
    labels = List.replicate 6 .tau ++ trailing ∧
    OccurrenceTransport profile ready base bindings entry peerEntry (List.replicate 9 .tau) (List.replicate 5 .tau)
      left right [some (.active 0 0)] ∧
    left.host = (start.host.enter name kind args).record reply.1 ∧ right.host = incoming.host ∧
    left.ctl = check.control (.pure (.flat reply.2)) ∧ right.ctl = canon.control (.pure (.flat reply.2)) ∧
    PairedComponentSite older left right check canon ∧ Steps profile ready (specDispatch ready base) left trailing finish

/-- The direct dispatcher reads the active thread and live store before
entering either embedder body. At a host frame, continue to its refusal. -/
def DirectGivePreludeCut (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (name : String) (kind : V1.FuncType)
    (args : List FlatValue) (destination : RecordDestination) (schema : Option Stored.TypeOf)
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (entry peerEntry start incoming : Config (core3 grow) (HostState sig)) (labels : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig)) : Prop :=
  ComponentEarlyPrefix profile ready base bindings older check canon start incoming labels finish 2 ∨
    ∃ trailing left right,
      labels = [.tau, .tau] ++ trailing ∧ left.host = start.host ∧ right.host = incoming.host ∧
      left.store = start.store ∧ right.store = incoming.store ∧
      left.ctl = check.control (calloutBody Limits.spec Quirks.none ready base left.store check.thread (.embedder name kind) args) ∧
      right.ctl = canon.control (calloutBody Limits.spec Quirks.none ready (LiveDispatch.host bindings base)
        right.store canon.thread (.embedder name kind) args) ∧
      PairedComponentSite older left right check canon ∧
      OccurrenceTransport profile ready base bindings entry peerEntry [.tau, .tau, .tau] [.tau, .tau, .tau]
        left right [some (.active 0 0)] ∧
      VisitorWriterPath profile ready base bindings entry peerEntry [.tau, .tau, .tau] [.tau, .tau, .tau] left right ∧
      Steps profile ready (specDispatch ready base) left trailing finish ∧
      (check.thread = none → canon.thread = none →
        DirectHostRefusalCut profile ready base bindings older name kind args destination schema
          check canon entry peerEntry left right trailing finish)

/-- Replay the exact extracted prefix, including silent steps. The selected
mark can move between active and saved storage or disappear; all other
locations also retain their actual scheduler paths. -/
def ActualCallbackReplay (bindings : List (Binding sig)) (profile : ProfileKind)
    (ready : HostReady (HostState sig)) (base : HostImpl (core3 grow) (HostState sig))
    (protectedReturn : ReturnFrame.Continuation (core3 grow) (HostState sig) → Prop)
    (start : Config (core3 grow) (HostState sig)) (labels : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig)) : Prop :=
  open ReturnFrame.Occurrence in
  ∀ {changes retained peer mark}, (∀ first second, changes first second → protectedReturn first) →
    HostFrame.Related.Paired changes start peer → Outside retained (segmentStorage start) (segmentStorage peer) mark →
    ∃ reached finalMark,
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) peer labels reached ∧
      HostFrame.Related.Paired changes finish reached ∧
      Outside retained (segmentStorage finish) (segmentStorage reached) finalMark ∧
      Trail profile ready (specDispatch ready base) start mark labels finish finalMark ∧
      Trail profile ready (specDispatch ready (LiveDispatch.host bindings base)) peer mark labels reached finalMark ∧
      CoupledOccurrencePaths profile ready base bindings start peer labels labels finish reached ∧
      OccurrenceTransport profile ready base bindings start peer labels labels finish reached ∧
      CheckedSpendFlow start.host.writer peer.host.writer finish.host.writer reached.host.writer [] ∧
      WriterPath profile ready (specDispatch ready base) start labels finish [] ∧
      WriterPath profile ready (specDispatch ready (LiveDispatch.host bindings base)) peer labels reached []

/-- Extract a closed prefix from the actual finite derivation, leaving any
boundary action and the rest of the checked run at their original states. -/
inductive ClassifiedCallbackRun (bindings : List (Binding sig)) (profile : ProfileKind)
    (ready : HostReady (HostState sig)) (base : HostImpl (core3 grow) (HostState sig))
    (protectedReturn : ReturnFrame.Continuation (core3 grow) (HostState sig) → Prop)
    (start : Config (core3 grow) (HostState sig)) (labels : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig)) : Prop where
  | complete (closed : ClosedCallbackPrefix bindings profile ready base protectedReturn start (PayloadPrefix.visible labels) finish)
      (replay : ActualCallbackReplay bindings profile ready base protectedReturn start labels finish)
      (growing : CoreGrowthSteps profile ready (specDispatch ready base) start labels finish)
  | boundary {leading label trailing reached next}
      (split : labels = leading ++ label :: trailing)
      (closed : ClosedCallbackPrefix bindings profile ready base protectedReturn start (PayloadPrefix.visible leading) reached)
      (growing : CoreGrowthSteps profile ready (specDispatch ready base) start leading reached)
      (replay : ActualCallbackReplay bindings profile ready base protectedReturn start leading reached)
      (cut : CallbackWorkerBoundary bindings ready (specDispatch ready base) protectedReturn reached label next)
      (actual : Step profile ready (specDispatch ready base) reached label next)
      (tail : Steps profile ready (specDispatch ready base) next trailing finish)

/-- The installed allocator occurrence migrates through actual scheduler
edits. Older substitutions remain valid off that mark, even if it is lost
to a trap or the callback is still suspended. -/
structure AllocatorMark (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (checkEntry canonEntry : Config (core3 grow) (HostState sig)) (checkTrace canonTrace : Trace grow sig)
    (checked canonical : Config (core3 grow) (HostState sig)) (mark : Option ReturnFrame.Occurrence.Location) : Prop where
  outside : ReturnFrame.Occurrence.Outside older (ReturnFrame.Occurrence.segmentStorage checked)
    (ReturnFrame.Occurrence.segmentStorage canonical) mark
  checkedTrail : ReturnFrame.Occurrence.Trail profile ready (specDispatch ready base)
    checkEntry (some (.active 0 0)) checkTrace checked mark
  canonicalTrail : ReturnFrame.Occurrence.Trail profile ready (specDispatch ready (LiveDispatch.host bindings base))
    canonEntry (some (.active 0 0)) canonTrace canonical mark
  movement : CoupledOccurrencePaths profile ready base bindings checkEntry canonEntry checkTrace canonTrace checked canonical

/-- Follow an actual allocation install into an extracted finite callback.
The newly installed occurrence is tracked separately from the enclosing
ones; each may independently move or be lost. -/
def ActualAllocatorOccurrencePrefix (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older changes : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (left right checkEntry canonEntry : Config (core3 grow) (HostState sig))
    (checkInstall canonInstall callback : Trace grow sig) (checked : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ canonical mark, HostFrame.Related.Paired changes checked canonical ∧
    AllocatorMark profile ready base bindings older checkEntry canonEntry callback callback checked canonical mark ∧
    OccurrenceTransport profile ready base bindings left right (checkInstall ++ callback) (canonInstall ++ callback)
      checked canonical [mark] ∧
    CheckedSpendFlow checkEntry.host.writer canonEntry.host.writer checked.host.writer canonical.host.writer []

def stringAllocatorEntry (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (cx : LiftLowerContext (core3 grow)) (ptr : Nat) (oldSize : Option Nat) (alignment : ABI.Alignment) (size : Nat)
    (state : Config (core3 grow) (HostState sig)) (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (resume : ReturnFrame.Continuation (core3 grow) (HostState sig)) : Config (core3 grow) (HostState sig) :=
  let request := Call.reallocate cx (oldSize.elim 0 (fun _ => ptr)) (oldSize.getD 0) alignment.bytes size
  { state with ctl := { cursor with frames := .prog resume :: cursor.frames }.control (dispatch request) }

/-- The executed part of a callback. Its checked and canonical traces are
indexed separately; the reached pair keeps the actual journals. -/
structure ExecutedCallbackSegment (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (changes : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (checked canonical : Config (core3 grow) (HostState sig)) (checkLabels canonLabels : Trace grow sig)
    (finish peer : Config (core3 grow) (HostState sig)) : Prop where
  checkedRun : CoreGrowthSteps profile ready (specDispatch ready base) checked checkLabels finish
  observed : PayloadPrefix.visible canonLabels = PayloadPrefix.visible checkLabels
  paired : HostFrame.Related.Paired changes finish peer
  occurrences : OccurrenceTransport profile ready base bindings checked canonical checkLabels canonLabels finish peer
  writers : VisitorWriterPath profile ready base bindings checked canonical checkLabels canonLabels finish peer

abbrev CallbackPathIndex (grow : SingleThreaded.GrowOracle) (sig : Signature) :=
  Option (Trace grow sig × Trace grow sig × Config (core3 grow) (HostState sig))

def CallbackPathIndex.Matches (index : CallbackPathIndex grow sig)
    (checked canonical : Trace grow sig) (peer : Config (core3 grow) (HostState sig)) : Prop :=
  match index with
  | none => True
  | some executed => executed = (checked, canonical, peer)

/-- The callback evidence shared by string and collection traversal. In the
executed case the two prefixes may have different silent steps. Growth is
certified at reached updates on the checked prefix; the journals need not
be preserved. Neither case asserts that the installed occurrence returns. -/
inductive AllocatorCallbackPrefix (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (first second : ReturnFrame.Continuation (core3 grow) (HostState sig))
    (checked canonical : Config (core3 grow) (HostState sig)) :
    CallbackPathIndex grow sig → Trace grow sig → Config (core3 grow) (HostState sig) → Prop where
  | closed {seen finish} (path : ClosedCallbackPrefix bindings profile ready base
      (fun resume => (∃ peer, older resume peer) ∨ resume = first) checked seen finish) :
      AllocatorCallbackPrefix profile ready base bindings older first second checked canonical none seen finish
  | executed {checkLabels canonLabels finish peer}
      (run : ExecutedCallbackSegment profile ready base bindings (ReturnFrame.Extend older first second)
        checked canonical checkLabels canonLabels finish peer) :
      AllocatorCallbackPrefix profile ready base bindings older first second checked canonical
        (some (checkLabels, canonLabels, peer)) (PayloadPrefix.visible checkLabels) finish

/-- Cut a growing checked derivation at the first action not covered by
closed replay. No part of a boundary action is replayed by this cut. -/
inductive ExecutedCallbackCut (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (changes : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (checked canonical : Config (core3 grow) (HostState sig)) (actual : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig)) : Prop where
  | complete {peer} (segment : ExecutedCallbackSegment profile ready base bindings changes checked canonical actual actual finish peer)
      (writers : CheckedSpendFlow checked.host.writer canonical.host.writer finish.host.writer peer.host.writer [])
  | boundary {leading label trailing reached peer next}
      (split : actual = leading ++ label :: trailing)
      (segment : ExecutedCallbackSegment profile ready base bindings changes checked canonical leading leading reached peer)
      (writers : CheckedSpendFlow checked.host.writer canonical.host.writer reached.host.writer peer.host.writer [])
      (kind : CallbackWorkerBoundary bindings ready (specDispatch ready base) (fun resume => ∃ rhs, changes resume rhs) reached label next)
      (step : Step profile ready (specDispatch ready base) reached label next)
      (tail : Steps profile ready (specDispatch ready base) next trailing finish)
      (smaller : trailing.length < actual.length)

/-- The remaining checked execution, with a source-certified terminal
pop or lockdown step when the raw program is still pending. -/
inductive CheckedTerminalWriterTail (profile : ProfileKind) (ready : HostReady (HostState sig))
    (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (start : Config (core3 grow) (HostState sig)) : Trace grow sig → Config (core3 grow) (HostState sig) → Prop where
  | residual {labels finish} (run : Steps profile ready dispatch start labels finish) :
      CheckedTerminalWriterTail profile ready dispatch start labels finish
  | executed {label next labels finish} (step : Step profile ready dispatch start label next)
      (edit : ReturnFrame.Occurrence.transitionEdit start label = .pop ∨
        ReturnFrame.Occurrence.transitionEdit start label = .clear)
      (writer : next.host.writer = start.host.writer)
      (run : Steps profile ready dispatch next labels finish) :
      CheckedTerminalWriterTail profile ready dispatch start (label :: labels) finish

/-- A typed give reply executed only on the checked side. The canonical
trace ends at the reached pending configuration, not at a matching pop. -/
def CheckedOnlyGiveReply (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (route : GiveEffectRoute) (destination : RecordDestination) (ticket : Nat)
    (issue : Stored.Endpoints.RecordLower.Issue)
    (start incoming left right : Config (core3 grow) (HostState sig))
    (checkLeading canonLeading trailing : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  open ReturnFrame.Occurrence in
  ∃ suffix checked,
    trailing = [.tau, .tau, .tau] ++ suffix ∧
    Steps profile ready (specDispatch ready base) start checkLeading left ∧
    Steps profile ready (specDispatch ready base) left [.tau, .tau, .tau] checked ∧
    Steps profile ready (specDispatch ready base) checked suffix finish ∧
    checked.store = left.store ∧
    checked.host = left.host.record (route.reply destination ticket (.error issue)).1 ∧
    Plain.HostFramedSteps HostState.writer profile ready (specDispatch ready base) left [.tau, .tau, .tau] checked ∧
    (∃ written,
      (∀ place, Prefix profile ready (specDispatch ready base) left place [.tau, .tau] written place) ∧
      Plain.HostFramedSteps HostState.writer profile ready (specDispatch ready base) left [.tau, .tau] written ∧
      Step profile ready (specDispatch ready base) written .tau checked ∧ transitionEdit written .tau = .pop) ∧
    ∀ cursor : Option Location, ∃ checkedMark canonMark,
      Trail profile ready (specDispatch ready base) start cursor (checkLeading ++ [.tau, .tau, .tau]) checked checkedMark ∧
      Trail profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming cursor canonLeading right canonMark

/-- A checked trace may reach an open store update that cannot be used to
transport a linked-memory width. This is a comparison boundary, not a
runtime refusal, and does not require later updates to preserve growth. -/
def ReachedNonGrowingUpdate (profile : ProfileKind) (ready : HostReady (HostState sig))
    (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (start : Config (core3 grow) (HostState sig)) (labels : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ leading label trailing reached next,
    labels = leading ++ label :: trailing ∧ CoreGrowthSteps profile ready dispatch start leading reached ∧
    ¬ CoreUpdateGrows reached ∧ Step profile ready dispatch reached label next ∧ Steps profile ready dispatch next trailing finish

def workerBranchLabel : Label (core3 grow) (HostState sig) → Prop
  | .choice _ _ | .host _ => True
  | _ => False

/-- A finite checked completion prefix with the Core caller still present. -/
structure CheckedCoreReplyPrefix (profile : ProfileKind) (ready : HostReady (HostState sig))
    (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (start : Config (core3 grow) (HostState sig)) (actual : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig)) : Prop where
  short : actual.length < 3
  quiet : PayloadPrefix.visible actual = []
  store : finish.store = start.store
  writers : WriterPath profile ready dispatch start actual finish []
  paths : ∀ place, ReturnFrame.Occurrence.Prefix profile ready dispatch start place actual finish place

/-- A recursive body stopped before a common caller reply. A local branch
retains the reached checked action, not an invented canonical action. -/
inductive GiveBodyStop (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig))
    (left right : Config (core3 grow) (HostState sig)) (trailing : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig)) (caller : Option ReturnFrame.Occurrence.Location) : Prop where
  | trap (leftLocked : left.ctl = []) (rightLocked : right.ctl = [])
  | localPrefix {target remaining} (nonempty : remaining ≠ [])
      (tail : Steps profile ready (specDispatch ready base) finish remaining target)
  | localChoice {leading taken suffix middle next} (split : trailing = leading ++ taken :: suffix)
      (choice : workerBranchLabel taken) (shared : Steps profile ready (specDispatch ready base) left leading middle)
      (step : Step profile ready (specDispatch ready base) middle taken next)
      (tail : Steps profile ready (specDispatch ready base) next suffix finish)
  | allocatorInstall (exhausted : trailing = [])
  | coreReplyPrefix (refusal : Option Stored.Endpoints.RecordLower.Issue)
      (reached : CheckedCoreReplyPrefix profile ready (specDispatch ready base) left trailing finish)
  | callerNotTop (refusal : Option Stored.Endpoints.RecordLower.Issue) (missing : caller ≠ some (.active 0 0))

/-- The part of a give actually compared, rebased through its own entry.
Both trails end before executing the checked residual. -/
structure GiveBodyCut (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (start peer left right : Config (core3 grow) (HostState sig))
    (checked canonical trailing : Trace grow sig) (finish : Config (core3 grow) (HostState sig))
    (marks : List (Option ReturnFrame.Occurrence.Location)) : Prop where
  observed : PayloadPrefix.visible checked = PayloadPrefix.visible canonical
  store : left.store = right.store
  paths : OccurrenceTransport profile ready base bindings start peer checked canonical left right marks
  residual : Steps profile ready (specDispatch ready base) left trailing finish
  writers : VisitorWriterPath profile ready base bindings start peer checked canonical left right

open ReturnFrame.Occurrence in
/-- The checked-only completion of a direct give. A finite prefix before
the program pop retains its mark; only the actual pop may lose that mark and
start the original caller with the recorded reply. -/
inductive CheckedProgramReplyCut (profile : ProfileKind) (ready : HostReady (HostState sig))
    (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))) (start : Config (core3 grow) (HostState sig))
    (caller : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (resume : ReturnFrame.Continuation (core3 grow) (HostState sig)) (reply : Event × List FlatValue) :
    Trace grow sig → Config (core3 grow) (HostState sig) → Prop where
  | prefix {actual finish} (short : actual.length < 3)
      (quiet : PayloadPrefix.visible actual = []) (store : finish.store = start.store)
      (writers : WriterPath profile ready dispatch start actual finish [])
      (paths : ∀ place, Prefix profile ready dispatch start place actual finish place) :
      CheckedProgramReplyCut profile ready dispatch start caller resume reply actual finish
  | popped {trailing finish}
      (written : ∀ place, Prefix profile ready dispatch start place [.tau, .tau]
        { start with
          host := start.host.record reply.1
          ctl := { caller with frames := .prog resume :: caller.frames }.control (.pure (.flat reply.2)) } place)
      (writers : WriterPath profile ready dispatch start [.tau, .tau]
        { start with host := start.host.record reply.1
                     ctl := { caller with frames := .prog resume :: caller.frames }.control (.pure (.flat reply.2)) } [])
      (remaining : Steps profile ready dispatch
        { start with
          host := start.host.record reply.1
          ctl := { caller with frames := .prog resume :: caller.frames }.control (.pure (.flat reply.2)) } (.tau :: trailing) finish)
      (paths : ∀ mark, Trail profile ready dispatch start mark [.tau, .tau, .tau]
        { start with host := start.host.record reply.1, ctl := caller.control (resume (.flat reply.2)) }
        (mark.bind (Edit.pop : Edit (core3 grow) (HostState sig)).follow))
      (residual : Steps profile ready dispatch
        { start with host := start.host.record reply.1, ctl := caller.control (resume (.flat reply.2)) } trailing finish) :
      CheckedProgramReplyCut profile ready dispatch start caller resume reply ([.tau, .tau, .tau] ++ trailing) finish

open ReturnFrame.Occurrence in
/-- Placement is an actual checked path. The canonical program stays
pending; a placement fault alone does not evidence a canonical fault. -/
inductive DirectGivePlacementCut (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (start peer : Config (core3 grow) (HostState sig))
    (caller : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (resume : ReturnFrame.Continuation (core3 grow) (HostState sig))
    (request : GiveSelector bindings) (ticket : Nat) (selected : SelectionValue sig request.schema)
    (field : Stored.Endpoints.RecordLower.Field) : Trace grow sig → Config (core3 grow) (HostState sig) → Prop where
  | prefix {actual finish}
      (paths : ∀ place, Prefix profile ready (specDispatch ready base) start place actual finish place)
      (writers : WriterPath profile ready (specDispatch ready base) start actual finish [])
      (pending : ∃ suffix, suffix ≠ [] ∧ ∃ target, Steps profile ready (specDispatch ready base) finish suffix target) :
      DirectGivePlacementCut profile ready base bindings start peer caller resume request ticket selected field actual finish
  | trapped {reason count beforeTrap trailing finish}
      (placement : request.selectedPlacement selected start.store = .error reason)
      (preTrap : PayloadPrefix.PlacementFault profile ready (specDispatch ready base) start beforeTrap count reason)
      (readWriters : WriterPath profile ready (specDispatch ready base) start (List.replicate count .tau) beforeTrap [])
      (paths : ∀ mark, Trail profile ready (specDispatch ready base) start mark (List.replicate count .tau ++ [.trap reason])
        (StepDefs.trapCfg start) (mark.bind (Edit.clear : Edit (core3 grow) (HostState sig)).follow))
      (writers : WriterPath profile ready (specDispatch ready base) start (List.replicate count .tau ++ [.trap reason])
        (StepDefs.trapCfg start) [])
      (residual : Steps profile ready (specDispatch ready base) (StepDefs.trapCfg start) trailing finish) :
      DirectGivePlacementCut profile ready base bindings start peer caller resume request ticket selected field
        ((List.replicate count .tau ++ [.trap reason]) ++ trailing) finish
  | reached {used trailing finish}
      (after : Config (core3 grow) (HostState sig))
      (focus : after = { start with
        ctl := { caller with frames := .prog resume :: caller.frames }.control (request.fieldContinuation ticket selected field) })
      (placement : request.selectedPlacement selected start.store = .ok ())
      (paths : ∀ place, Prefix profile ready (specDispatch ready base) start place used after place)
      (writers : WriterPath profile ready (specDispatch ready base) start used after [])
      (quiet : PayloadPrefix.visible used = [])
      (residual : Steps profile ready (specDispatch ready base) after trailing finish) :
      DirectGivePlacementCut profile ready base bindings start peer caller resume request ticket selected field (used ++ trailing) finish

open ReturnFrame.Occurrence in
/-- A finite cut at the real width read. Fit is decided in the reached
continuation; the peer still has its original canonical program pending. -/
inductive DirectGiveWidthCut (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (start peer : Config (core3 grow) (HostState sig))
    (caller : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (resume : ReturnFrame.Continuation (core3 grow) (HostState sig))
    (request : GiveSelector bindings) (ticket : Nat) (selected : SelectionValue sig request.schema)
    (field : Stored.Endpoints.RecordLower.Field) : Trace grow sig → Config (core3 grow) (HostState sig) → Prop where
  | prefix (paths : OccurrenceTransport profile ready base bindings start peer [] [] start peer) :
      DirectGiveWidthCut profile ready base bindings start peer caller resume request ticket selected field [] start
  | reached {trailing finish}
      (after : Config (core3 grow) (HostState sig))
      (focus : after = { start with
        ctl := { caller with frames := .prog resume :: caller.frames }.control
          (request.measuredContinuation ticket selected field (ptrTypeIn start.store (request.destination.context request.inst))) })
      (paths : ∀ place, Prefix profile ready (specDispatch ready base) start place [.tau] after place)
      (writers : WriterPath profile ready (specDispatch ready base) start [.tau] after [])
      (residual : Steps profile ready (specDispatch ready base) after trailing finish)
      (decision : let width := ptrTypeIn start.store (request.destination.context request.inst)
        (request.selectedFits selected width = false ∧
          CheckedProgramReplyCut profile ready (specDispatch ready base) after caller resume
            (giveAdmissionReply ticket request.destination request.schema (.lowerPayload (.preflight (.abi .allocationPrecondition))))
            trailing finish) ∨
        (request.selectedFits selected width = true ∧
          after.ctl = { caller with frames := .prog resume :: caller.frames }.control
            (request.placementContinuation ticket selected field width) ∧
          DirectGivePlacementCut profile ready base bindings after peer caller resume request ticket selected field trailing finish)) :
      DirectGiveWidthCut profile ready base bindings start peer caller resume request ticket selected field (.tau :: trailing) finish

open ReturnFrame.Occurrence in
/-- A finite checked cut at the compiled root's preparation reads. No
canonical step is spent by these checked-only reads. -/
inductive DirectGivePreparationCut (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (start peer : Config (core3 grow) (HostState sig))
    (caller : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (resume : ReturnFrame.Continuation (core3 grow) (HostState sig))
    (request : GiveSelector bindings) (ticket : Nat) (selected : SelectionValue sig request.schema)
    (field : Stored.Endpoints.RecordLower.Field) : Trace grow sig → Config (core3 grow) (HostState sig) → Prop where
  | prefix {actual finish} (short : actual.length < 2)
      (paths : OccurrenceTransport profile ready base bindings start peer actual [] finish peer)
      (writers : WriterPath profile ready (specDispatch ready base) start actual finish []) :
      DirectGivePreparationCut profile ready base bindings start peer caller resume request ticket selected field actual finish
  | reached {trailing finish}
      (after : Config (core3 grow) (HostState sig))
      (focus : after = { start with
        ctl := { caller with frames := .prog resume :: caller.frames }.control
          (request.preparedContinuation ticket selected field (Record.prepare start.store start.host.writer field.objects)) })
      (read : ∃ reader, ExecutedPrepareRead profile ready base start reader after peer [.tau] field.objects)
      (paths : ∀ place, Prefix profile ready (specDispatch ready base) start place [.tau, .tau] after place)
      (writers : WriterPath profile ready (specDispatch ready base) start [.tau, .tau] after [])
      (residual : Steps profile ready (specDispatch ready base) after trailing finish)
      (refused : ∀ issue, Record.prepare start.store start.host.writer field.objects = .error issue →
        CheckedProgramReplyCut profile ready (specDispatch ready base) after caller resume
          (giveAdmissionReply ticket request.destination request.schema (.lowerPayload issue)) trailing finish)
      (prepared : Record.prepare start.store start.host.writer field.objects = .ok () →
        DirectGiveWidthCut profile ready base bindings after peer caller resume request ticket selected field trailing finish) :
      DirectGivePreparationCut profile ready base bindings start peer caller resume request ticket selected field
        ([.tau, .tau] ++ trailing) finish

/-- An actual pair of registration reads selected different branches from the two raw
writers. These are continuation focuses, not executed replies or fabricated traps. -/
def ReachedRegistrationMismatch (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (left right : Config (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (leftTicket rightTicket : Nat) (caller : CallerId) (tree : Stored.OwnedMemory.Tree sig) : Prop :=
  ∃ beforeLeft beforeRight,
    RegistrationProbeMismatch beforeLeft beforeRight left right check canon leftTicket rightTicket (some caller) tree ∧
    OccurrenceTransport profile ready base bindings beforeLeft beforeRight [.tau] [.tau] left right ∧
    WriterPath profile ready (specDispatch ready base) beforeLeft [.tau] left [] ∧
    WriterPath profile ready (specDispatch ready (LiveDispatch.host bindings base)) beforeRight [.tau] right []

open Stored.OwnedMemory.Claims Stored.OwnedMemory.Claims.Record in
/-- The two executed prepare reads frame their actual writers. The discrepancy
is in a visited dry-run demand, not in an unexecuted write or caller reply. -/
def ReachedRecordPrepareMismatch (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (left right reached peer : Config (core3 grow) (HostState sig))
    (plan : List Stored.Endpoints.RecordLower.Object)
    (next : Except Stored.Endpoints.RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (pending : Spend → Prop) : Prop :=
  ∃ thread lhsFrames lhsRest rhsFrames rhsRest,
    left.ctl = ⟨thread, .prog (.op .hostGet (fun state => next (prepare left.store state.writer plan))), lhsFrames⟩ :: lhsRest ∧
    right.ctl = ⟨thread, .prog (.op .hostGet (fun state => next (prepare left.store state.writer plan))), rhsFrames⟩ :: rhsRest ∧
    reached.ctl = ⟨thread, .prog (next (prepare left.store left.host.writer plan)), lhsFrames⟩ :: lhsRest ∧
    peer.ctl = ⟨thread, .prog (next (prepare left.store right.host.writer plan)), rhsFrames⟩ :: rhsRest ∧
    OccurrenceTransport profile ready base bindings left right [.tau] [.tau] reached peer ∧
    WriterPath profile ready (specDispatch ready base) left [.tau] reached [] ∧
    WriterPath profile ready (specDispatch ready (LiveDispatch.host bindings base)) right [.tau] peer [] ∧
    reached.host.writer.ClaimDiscrepancies peer.host.writer pending ∧
    prepare left.store left.host.writer plan ≠ prepare left.store right.host.writer plan ∧
    ∃ probe, pending probe ∧ ReachedPrepareConflict left.store left.host.writer right.host.writer plan probe

/-- The actual on-start call installed this return occurrence, which survived
the caller reads and was popped at the designated worker cursor. -/
structure SharedLiftOnStartPop (reads : Nat) (profile : ProfileKind) (ready : HostReady (HostState sig))
    (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) (caller : CallerId)
    (resume : ReturnFrame.Continuation (core3 grow) (HostState sig)) (args : List Value.Val)
    (after : Config (core3 grow) (HostState sig)) : Prop where
  executed : ∃ before entered returned,
    before.ctl = cursor.control (.op (.call (.onStart caller)) resume) ∧
    Step profile ready dispatch before .tau entered ∧
    entered.ctl = { cursor with frames := .prog resume :: cursor.frames }.control (dispatch (.onStart caller)) ∧
    ReturnFrame.Occurrence.Prefix profile ready dispatch entered (.active 0 0) (List.replicate reads .tau) returned (.active 0 0) ∧
    returned.ctl = { cursor with frames := .prog resume :: cursor.frames }.control (.pure (.vals args)) ∧
    Step profile ready dispatch returned .tau after

abbrev SharedDestructorOnStartPop := SharedLiftOnStartPop (grow := grow) (sig := sig) 3

/-- The original onResolve return segment survived the caller reads and real
result assignment, then popped on the reached execution. -/
structure SharedRecordAllocatorResolvePop (profile : ProfileKind) (ready : HostReady (HostState sig))
    (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (task : TaskId) (caller : CallerId) (value : Value.Val) (after : Config (core3 grow) (HostState sig)) : Prop where
  executed : ∃ before entered returned,
    let resume := sharedDestructorResolveReply (sig := sig) task
    let call := Call.onResolve (E := core3 grow) caller (some [value])
    before.ctl = cursor.control (.op (.call call) resume) ∧
    Step profile ready dispatch before .tau entered ∧
    entered.ctl = { cursor with frames := .prog resume :: cursor.frames }.control (dispatch call) ∧
    ReturnFrame.Occurrence.Prefix profile ready dispatch entered (.active 0 0) [.tau, .tau, .tau] returned (.active 0 0) ∧
    returned.store = ArenaOps.updateSt ArenaField.callers caller (LiftSt.recordReallocResult value) entered.store ∧
    returned.ctl = { cursor with frames := .prog resume :: cursor.frames }.control (.pure .unit) ∧
    Step profile ready dispatch returned .tau after

/-- The reached destructor task and the actual caller object it names. -/
def SharedDestructorTaskSource (task : TaskId) (store : CStore (core3 grow)) : Prop :=
  ∃ (record : Task (core3 grow)) (width : AddrType) (rep : Nat),
    ArenaField.tasks.get? store task = some record ∧ record.ft = dtorType width ∧ record.opts = {} ∧
    ArenaField.callers.get? store record.caller = some (.sub (.destructor rep))

/-- The registered worker still names the task and caller created by the
source destructor setup. Reads at this entry use these actual reached stores. -/
structure SharedDestructorRegisteredSource (task : TaskId) (checked canonical : CStore (core3 grow)) : Prop where
  paired : checked = canonical
  entry : SharedDestructorTaskSource task checked

/-- The worker's dormant parents run the same source lift loop with separate
completion continuations and the original enclosing caller frames. -/
inductive DestructorParentChain (changes : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (body : ThreadBody (core3 grow)) :
    List (Activation (core3 grow) (HostState sig)) → List (Activation (core3 grow) (HostState sig)) → Prop where
  | paired {thread frame frames peerFrames rest peerRest leftTicket rightTicket}
      (framesPaired : List.Forall₂ (ReturnFrame.Related.Segment changes) frames peerFrames)
      (restPaired : List.Forall₂ (ReturnFrame.Related.Active changes) rest peerRest)
      (tickets : leftTicket ≠ rightTicket) :
      DestructorParentChain changes body
        ((PayloadPrefix.Cursor.mk thread (frame :: frames) rest).control (sharedDestructorAfterResume body leftTicket))
        ((PayloadPrefix.Cursor.mk thread (frame :: peerFrames) peerRest).control (sharedDestructorAfterResume body rightTicket))

/-- Compiler evidence retained at a reached allocating visitor. -/
abbrev SourceOverlayFieldSource (destination : RecordDestination) (item : Stored.Endpoints.RecordLower.Field) : Prop :=
  ∃ (root : Stored.Endpoints.RecordLower.Field) (schema : Stored.TypeOf),
  root.LayoutMatches schema ∧ root.Emitted ∧
  Stored.Lower.fits Quirks.none destination.encoding destination.width schema root.value = true ∧
  Stored.Endpoints.RecordLower.Field.AllocatorFor destination.realloc root ∧ root.Descendant item

/-- The two value shapes that use a canonical indirect list store. Map entries
have a captured layout and their own executable key and value placements. -/
inductive CanonicalListStore where
  | list (element : Stored.TypeOf)
  | map (key : WIT.KeyType) (value : Stored.TypeOf)

def CanonicalListStore.layout (site : CanonicalListStore) (width : AddrType) : ABI.Layout :=
  match site with
  | .list element => ABI.layout width element
  | .map key value => ABI.layout width (.record (ABI.mapEntryFields key value) : Stored.TypeOf)

def CanonicalListStore.storeEntry (site : CanonicalListStore) (cx : LiftLowerContext (core3 grow))
    (width : AddrType) (entry : Value.Val) (ptr : Nat) : Session grow sig Unit :=
  match site with
  | .list element => Canon.store Limits.spec Quirks.none cx entry element ptr
  | .map key value =>
    match entry with
    | .record [entryKey, entryValue] => do
      let keyLayout := ABI.primitiveLayout width key.toPrimitive
      let keyAddr := ABI.alignTo ptr keyLayout.alignment
      storePrim Limits.spec Quirks.none cx key.toPrimitive entryKey keyAddr
      Canon.store Limits.spec Quirks.none cx entryValue value
        (ABI.alignTo (keyAddr + keyLayout.size) (ABI.layout width value).alignment)
    | _ => storeMismatch

/-- The request selected by the canonical list or map store at its width read. -/
def canonicalListStoreRequest (width : AddrType) (site : CanonicalListStore) (count : Nat) : ABI.ReallocRequest :=
  let area := site.layout width
  { oldPtr := 0, oldSize := 0, alignment := area.alignment.bytes, newSize := count * area.size }

/-- The canonical list either publishes a memory descriptor or passes flat
words to the original continuation at the enclosing lowering width. -/
inductive CanonicalListOutput (grow : SingleThreaded.GrowOracle) (sig : Signature) where
  | memory (dest : Nat) (next : Session grow sig (Ret (core3 grow)))
  | flat (width : AddrType) (next : List FlatValue → Session grow sig (Ret (core3 grow)))

def CanonicalListOutput.finish (output : CanonicalListOutput grow sig) (cx : LiftLowerContext (core3 grow)) (pointer count : Nat) :
    Session grow sig (Ret (core3 grow)) :=
  match output with
  | .memory dest next => storeListDescriptor cx pointer count dest >>= fun _ => next
  | .flat width next => next [ptrFlat width pointer, ptrFlat width count]

/-- The allocation layout stays captured through validation and each entry. -/
def canonicalListStoreAfterPointer (cx : LiftLowerContext (core3 grow)) (width : AddrType) (site : CanonicalListStore)
    (values : List Value.Val) (output : CanonicalListOutput grow sig) (ptr : Nat) :
    Session grow sig (Ret (core3 grow)) := do
  let area := site.layout width
  let checked ← validateListRange cx area values.length ptr
  storeListIntoValidRangeWith area.size (site.storeEntry cx width) values checked
  output.finish cx checked values.length

def canonicalListStoreResume (cx : LiftLowerContext (core3 grow)) (width : AddrType) (site : CanonicalListStore)
    (values : List Value.Val) (output : CanonicalListOutput grow sig) :
    ReturnFrame.Continuation (core3 grow) (HostState sig)
  | .nat pointer => canonicalListStoreAfterPointer cx width site values output pointer
  | _ => internal "late-bound call: expected Ret.nat"

def canonicalListStoreCall (cx : LiftLowerContext (core3 grow)) (width : AddrType) (site : CanonicalListStore)
    (values : List Value.Val) (output : CanonicalListOutput grow sig) : Session grow sig (Ret (core3 grow)) :=
  let request := canonicalListStoreRequest width site values.length
  .op (.call (.reallocate cx request.oldPtr request.oldSize request.alignment request.newSize))
    (canonicalListStoreResume cx width site values output)

/-- The completed string range is packed at the enclosing flat lowering
width, which is independent of the width used to select the encoding plan. -/
def canonicalFlatStringWords (cx : LiftLowerContext (core3 grow)) (sourceWidth resultWidth : AddrType)
    (value : Value.StrVal) (pointer : Nat) : List FlatValue :=
  let plan := storePlanFor Quirks.none cx.opts.encoding sourceWidth value
  [ptrFlat resultWidth pointer, ptrFlat resultWidth plan.taggedCodeUnits]

def canonicalFlatStringResume (cx : LiftLowerContext (core3 grow)) (sourceWidth resultWidth : AddrType)
    (value : Value.StrVal) (steps : List ABI.StoreStep) (next : List FlatValue → Session grow sig (Ret (core3 grow))) :
    ReturnFrame.Continuation (core3 grow) (HostState sig) :=
  PayloadPrefix.stringPlanResume cx steps (fun pointer => next (canonicalFlatStringWords cx sourceWidth resultWidth value pointer))

def canonicalFlatStringCall (cx : LiftLowerContext (core3 grow)) (sourceWidth resultWidth : AddrType)
    (value : Value.StrVal) (steps : List ABI.StoreStep) (old : Option Nat) (pointer : Nat)
    (alignment : ABI.Alignment) (size : Nat) (next : List FlatValue → Session grow sig (Ret (core3 grow))) :
    Session grow sig (Ret (core3 grow)) :=
  .op (.call (.reallocate cx (old.elim 0 (fun _ => pointer)) (old.getD 0) alignment.bytes size))
    (canonicalFlatStringResume cx sourceWidth resultWidth value steps next)

open Stored.Endpoints in
/-- The return programs installed by a source allocator call. -/
inductive SourceAllocatorReturn :
    ReturnFrame.Continuation (core3 grow) (HostState sig) →
    ReturnFrame.Continuation (core3 grow) (HostState sig) → Prop where
  | record (cx : LiftLowerContext (core3 grow)) (site : SharedRecordAllocation)
      (leftNext rightNext : Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
      (compiled : site.compiled cx) :
      SourceAllocatorReturn (site.resume cx leftNext) (site.resume cx rightNext)
  | collection (destination : RecordDestination) (inst : InstId) (type element : Stored.TypeOf)
      (entries : List RecordLower.Field) (index : Nat) (output : Stored.Lower.Output)
      (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
      (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
      (matching : RecordLower.Field.EntriesMatch entries element)
      (source : SourceOverlayFieldSource destination (.dynamic type element entries)) :
      SourceAllocatorReturn
        (PayloadPrefix.checkedCollectionResume destination inst entries (ABI.layout destination.width element) index output checkNext)
        (PayloadPrefix.canonicalCollectionResume destination inst entries (ABI.layout destination.width element) output canonNext
          (RecordLower.CanonicalTree.EntryMode.forOutput destination.width type output))
  | string (destination : RecordDestination) (inst : InstId) (str : LinkedCallback.StringField)
      (source : SourceOverlayFieldSource destination str.field) (prior steps : List ABI.StoreStep)
      (old : Option Nat) (alignment : ABI.Alignment) (size : Nat)
      (compiled : (storePlanFor Quirks.none destination.encoding destination.width str.value).steps =
        prior ++ (old.elim (.allocate alignment size) (fun oldSize => .reallocate oldSize alignment size) :: steps))
      (first second : Nat → Session grow sig (Ret (core3 grow))) :
      SourceAllocatorReturn (PayloadPrefix.stringPlanResume (destination.context inst) steps first)
        (PayloadPrefix.stringPlanResume (destination.context inst) steps second)
  | canonicalList (cx : LiftLowerContext (core3 grow)) (width : AddrType) (site : CanonicalListStore)
      (values : List Value.Val) (output : CanonicalListOutput grow sig) :
      SourceAllocatorReturn (canonicalListStoreResume cx width site values output)
        (canonicalListStoreResume cx width site values output)

  | canonicalFlatString (cx : LiftLowerContext (core3 grow)) (sourceWidth resultWidth : AddrType)
      (value : Value.StrVal) (prior steps : List ABI.StoreStep) (old : Option Nat)
      (alignment : ABI.Alignment) (size : Nat)
      (compiled : (storePlanFor Quirks.none cx.opts.encoding sourceWidth value).steps =
        prior ++ (old.elim (.allocate alignment size) (fun oldSize => .reallocate oldSize alignment size) :: steps))
      (next : List FlatValue → Session grow sig (Ret (core3 grow))) :
      SourceAllocatorReturn (canonicalFlatStringResume cx sourceWidth resultWidth value steps next)
        (canonicalFlatStringResume cx sourceWidth resultWidth value steps next)

open Stored.Endpoints in
/-- Frames beneath a selected synchronous worker. Common loop tail calls
can add frames above the two source returns and compiled allocator frames. -/
inductive SourceLiftLoopFrames (changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)) :
    List (Seg (core3 grow) (HostState sig)) → List (Seg (core3 grow) (HostState sig)) → Prop where
  | paired {left right} (frames : List.Forall₂ (ReturnFrame.Related.Segment changes) left right) :
      SourceLiftLoopFrames changes left right
  | common {left right} (resume : ReturnFrame.Continuation (core3 grow) (HostState sig))
      (below : SourceLiftLoopFrames changes left right) :
      SourceLiftLoopFrames changes (.prog resume :: left) (.prog resume :: right)
  | destructor {left right} (leftTicket rightTicket : Nat) (below : SourceLiftLoopFrames changes left right) :
      SourceLiftLoopFrames changes (.prog (sharedDestructorParentReply leftTicket) :: left)
        (.prog (sharedDestructorParentReply rightTicket) :: right)
  | allocator {left right first second} (source : SourceAllocatorReturn first second)
      (below : SourceLiftLoopFrames changes left right) :
      SourceLiftLoopFrames changes (.prog first :: left) (.prog second :: right)

open Stored.Endpoints in
/-- Source-indexed dormant controls. Each layer keeps its own continuation
and encloses further source layers or ordinary paired activations. Lookup
facts about the task and caller belong to the reached store, outside this
control relation. -/
inductive SourceParentStack (changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)) :
    List (Activation (core3 grow) (HostState sig)) → List (Activation (core3 grow) (HostState sig)) → Prop where
  | paired {left right} (active : List.Forall₂ (ReturnFrame.Related.Active changes) left right) :
      SourceParentStack changes left right
  | prefixed {left right active peerActive}
      (activePaired : List.Forall₂ (ReturnFrame.Related.Active changes) active peerActive)
      (below : SourceParentStack changes left right) :
      SourceParentStack changes (active ++ left) (peerActive ++ right)
  | destructor {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
      (body : ThreadBody (core3 grow)) (leftTicket rightTicket : Nat)
      (thread : check.thread = canon.thread)
      (frames : List.Forall₂ (ReturnFrame.Related.Segment changes) check.frames canon.frames)
      (below : SourceParentStack changes check.rest canon.rest) :
      SourceParentStack changes (check.control (sharedDestructorAfterResume body leftTicket))
        (canon.control (sharedDestructorAfterResume body rightTicket))
  | allocator {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
      (cx : LiftLowerContext (core3 grow)) (task : TaskId) (caller : CallerId)
      (thread : check.thread = canon.thread)
      (frames : SourceLiftLoopFrames changes check.frames canon.frames)
      (below : SourceParentStack changes check.rest canon.rest) :
      SourceParentStack changes (check.control (sharedRecordAllocatorAfterResume cx task caller))
        (canon.control (sharedRecordAllocatorAfterResume cx task caller))

  | syncLift {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
      (task : TaskId) (thread : check.thread = canon.thread)
      (frames : SourceLiftLoopFrames changes check.frames canon.frames)
      (below : SourceParentStack changes check.rest canon.rest) :
      SourceParentStack changes (check.control (callRet (.loop (.syncLiftLoop task))))
        (canon.control (callRet (.loop (.syncLiftLoop task))))

/-- Data shared by the two schedulers independently of the active worker
and its ticket-specific dormant parents. -/
abbrev DestructorSchedulerAlignment (changes : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (left right : Config (core3 grow) (HostState sig)) : Prop :=
  List.Forall₂ (ReturnFrame.Related.Saved changes) left.conts right.conts ∧
    left.pending = right.pending ∧ left.results = right.results ∧ left.cancels = right.cancels

/-- The loop return and the enclosing parent occurrence start in adjacent
slots of the actual paired loop entries. Their trails can outlive scheduling
and reentry, and are independent of continuation equality elsewhere. -/
structure DestructorParentLoopFrames (first second : ReturnFrame.Continuation (core3 grow) (HostState sig))
    (enclosing : Seg (core3 grow) (HostState sig)) (left right : Config (core3 grow) (HostState sig)) : Prop where
  checkedLoop : ReturnFrame.Occurrence.segmentAt (ReturnFrame.Occurrence.segmentStorage left) (.active 0 0) = some (.prog first)
  canonicalLoop : ReturnFrame.Occurrence.segmentAt (ReturnFrame.Occurrence.segmentStorage right) (.active 0 0) = some (.prog second)
  checkedEnclosing : ReturnFrame.Occurrence.segmentAt (ReturnFrame.Occurrence.segmentStorage left) (.active 0 1) = some enclosing
  canonicalEnclosing : ReturnFrame.Occurrence.segmentAt (ReturnFrame.Occurrence.segmentStorage right) (.active 0 1) = some enclosing

/-- A source visit's original entry and the two programs it must enter
on publication. Nested visits carry their own entry and continuations. -/
structure SourcePublicationContinuation (grow : SingleThreaded.GrowOracle) (sig : Signature) where
  entry : Config (core3 grow) (HostState sig)
  check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)
  canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)
  output : Stored.Lower.Output
  checkNext : Except Stored.Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow))
  canonNext : output.Result → Session grow sig (Ret (core3 grow))

structure ReachedSourcePublication (continuation : SourcePublicationContinuation grow sig)
    (changes : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (left right : Config (core3 grow) (HostState sig)) where
  value : continuation.output.Result
  stores : left.store = right.store
  scheduler : DestructorSchedulerAlignment changes left right
  checked : left.ctl = continuation.check.control (continuation.checkNext (.ok value))
  canonical : right.ctl = continuation.canon.control (continuation.canonNext value)

/-- The terminal cut of a compared callback. In-body cuts keep the exact
give prefix before a residual; an inner allocator cut can itself diverge. -/
inductive CallbackSliceEnd (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig)) :
    ReturnFrame.Substitutions (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
    Config (core3 grow) (HostState sig) → Trace grow sig → Config (core3 grow) (HostState sig) → Prop where
  | exhausted {changes reached peer} : CallbackSliceEnd profile ready base bindings changes reached peer [] reached
  | boundary {changes reached peer label next trailing finish}
      (kind : CallbackWorkerBoundary bindings ready (specDispatch ready base) (fun resume => ∃ peer, changes resume peer)
        reached label next)
      (step : Step profile ready (specDispatch ready base) reached label next)
      (tail : Steps profile ready (specDispatch ready base) next trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer (label :: trailing) finish
  | observation {changes reached peer next otherNext trailing finish thread resume frames rest}
      (focus : reached.ctl = ⟨thread, .prog (.op .hostGet resume), frames⟩ :: rest)
      (different : resume reached.host ≠ resume peer.host)
      (paths : OccurrenceTransport profile ready base bindings reached peer [.tau] [.tau] next otherNext)
      (writers : VisitorWriterPath profile ready base bindings reached peer [.tau] [.tau] next otherNext)
      (tail : Steps profile ready (specDispatch ready base) next trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer (.tau :: trailing) finish
  | tickReadiness {changes reached peer next otherNext trailing finish}
      (focus : reached.ctl = [.ofProg none (sourceTickRead ready reached.store)])
      (mismatch : TickReadinessMismatch ready reached peer)
      (paths : OccurrenceTransport profile ready base bindings reached peer [.tau] [.tau] next otherNext)
      (writers : VisitorWriterPath profile ready base bindings reached peer [.tau] [.tau] next otherNext)
      (checked : next.ctl = [.ofProg none (sourceTickCandidates (reached.store.candidates (ready reached.host)))])
      (canonical : otherNext.ctl = [.ofProg none (sourceTickCandidates (peer.store.candidates (ready peer.host)))])
      (tail : Steps profile ready (specDispatch ready base) next trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer (.tau :: trailing) finish
  | pendingAssignment {changes reached peer left right leftTarget rightTarget next}
      (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
      (checked : left.ctl = check.control (.op (.hostSet leftTarget) (fun _ => next)))
      (canonical : right.ctl = canon.control (.op (.hostSet rightTarget) (fun _ => next)))
      (paths : OccurrenceTransport profile ready base bindings reached peer [.tau] [.tau] left right)
      (writers : left.host.writer = reached.host.writer ∧ right.host.writer = peer.host.writer) :
      CallbackSliceEnd profile ready base bindings changes reached peer [.tau] left
  | coreAcceptTerminal {changes reached peer left right leading live trailing finish marks}
      (paths : OccurrenceTransport profile ready base bindings reached peer leading live left right marks)
      (writers : VisitorWriterPath profile ready base bindings reached peer leading live left right)
      (residual : Steps profile ready (specDispatch ready base) left trailing finish)
      (ending : trailing = [] ∨ left.host.writer.accepted ≠ right.host.writer.accepted ∨
        (∃ beforeLeft beforeRight check canon leftTicket rightTicket tree,
          RegistrationProbeMismatch beforeLeft beforeRight left right check canon leftTicket rightTicket none tree) ∨
        (left.ctl = [] ∧ right.ctl = [])) :
      CallbackSliceEnd profile ready base bindings changes reached peer (leading ++ trailing) finish
  /-- A compared prefix followed by the actual remaining run. -/
  | comparedPrefix {changes reached peer left right leading live trailing finish marks}
      (paths : OccurrenceTransport profile ready base bindings reached peer leading live left right marks)
      (writers : VisitorWriterPath profile ready base bindings reached peer leading live left right)
      (ending : CallbackSliceEnd profile ready base bindings changes left right trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer (leading ++ trailing) finish
  /-- The actual shared allocator is compared under its two installed
  continuations. The marked callback ending retains the checked suffix. -/
  | sharedRecordAllocator {changes reached peer left right resumed canonical leading checked canonLabels trailing finish marks}
      {first second : ReturnFrame.Continuation (core3 grow) (HostState sig)} {mark}
      (paths : OccurrenceTransport profile ready base bindings reached peer leading leading left right marks)
      (writers : VisitorWriterPath profile ready base bindings reached peer leading leading left right)
      (marked : AllocatorMark profile ready base bindings changes left right checked canonLabels resumed canonical mark)
      (compared : ExecutedCallbackSegment profile ready base bindings (ReturnFrame.Extend changes first second)
        left right checked canonLabels resumed canonical)
      (ending : CallbackSliceEnd profile ready base bindings (ReturnFrame.Extend changes first second)
        resumed canonical trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer (leading ++ checked ++ trailing) finish
  /-- The original shared allocator occurrence popped in both actual runs.
  The reached continuations use the actual result and store. -/
  | sharedRecordAllocatorPop {changes reached peer left right beforeLeft beforeRight afterLeft afterRight
        leading checked canonical trailing finish marks}
      {first second : ReturnFrame.Continuation (core3 grow) (HostState sig)} {value}
      {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
      (marked : AllocatorMark profile ready base bindings changes left right checked canonical beforeLeft beforeRight
        (some (.active 0 0)))
      (checkedAt : beforeLeft.ctl = { check with frames := .prog first :: check.frames }.control (.pure value))
      (canonicalAt : beforeRight.ctl = { canon with frames := .prog second :: canon.frames }.control (.pure value))
      (checkedPop : Step profile ready (specDispatch ready base) beforeLeft .tau afterLeft)
      (canonicalPop : Step profile ready (specDispatch ready (LiveDispatch.host bindings base)) beforeRight .tau afterRight)
      (paths : OccurrenceTransport profile ready base bindings reached peer ((leading ++ checked) ++ [.tau])
        ((leading ++ canonical) ++ [.tau]) afterLeft afterRight marks)
      (writers : VisitorWriterPath profile ready base bindings reached peer ((leading ++ checked) ++ [.tau])
        ((leading ++ canonical) ++ [.tau]) afterLeft afterRight)
      (ending : CallbackSliceEnd profile ready base bindings changes afterLeft afterRight trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer (((leading ++ checked) ++ [.tau]) ++ trailing) finish
  | sharedRecordPrepareMismatch {changes reached peer left right leading live trailing finish marks}
      {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
      {beforeLeft beforeRight plan}
      (site : SharedRecordPrepareMismatch beforeLeft beforeRight left right plan check canon)
      (paths : OccurrenceTransport profile ready base bindings reached peer leading live left right marks)
      (writers : VisitorWriterPath profile ready base bindings reached peer leading live left right)
      (residual : Steps profile ready (specDispatch ready base) left trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer (leading ++ trailing) finish
  | sharedRecordOwnerMismatch {changes reached peer left right leading live trailing finish marks}
      {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)} {beforeLeft beforeRight receipt cx index ptr}
      (site : SharedRecordOwnerProbeMismatch beforeLeft beforeRight left right receipt cx index ptr check canon)
      (paths : OccurrenceTransport profile ready base bindings reached peer leading live left right marks)
      (writers : VisitorWriterPath profile ready base bindings reached peer leading live left right)
      (residual : Steps profile ready (specDispatch ready base) left trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer (leading ++ trailing) finish
  | sharedRecordEndpointMismatch {changes reached peer left right leading live trailing finish marks}
      {beforeLeft beforeRight site}
      (mismatch : SharedRecordEndpointMismatch profile ready base bindings site beforeLeft beforeRight left right)
      (paths : OccurrenceTransport profile ready base bindings reached peer leading live left right marks)
      (writers : VisitorWriterPath profile ready base bindings reached peer leading live left right)
      (residual : Steps profile ready (specDispatch ready base) left trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer (leading ++ trailing) finish
  /-- Both executable loader reads have run and selected different pending
  updates or results. Registration and the loader store writes are still pending. -/
  | legacyLoadMismatch {changes reached peer finish trailing beforeLeft beforeRight check canon leftTicket rightTicket
      name kind args inst loader}
      (source : LinkedCoreAcceptHistoryDemand bindings name kind args
        ⟨beforeLeft.store, beforeLeft.host.writer⟩ ⟨beforeRight.store, beforeRight.host.writer⟩ inst loader)
      (checked : CoreAcceptLoaderRead profile ready (specDispatch ready base) check leftTicket loader beforeLeft reached)
      (canonical : CoreAcceptLoaderRead profile ready (specDispatch ready (LiveDispatch.host bindings base))
        canon rightTicket loader beforeRight peer)
      (different : loader ⟨beforeLeft.store, beforeLeft.host.writer⟩ ≠ loader ⟨beforeRight.store, beforeRight.host.writer⟩)
      (residual : Steps profile ready (specDispatch ready base) reached trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer trailing finish
  /-- The source worker continues after the original onStart pop while its
  two ticket-specific parent programs are dormant. -/
  | sharedDropSource {changes reached peer trailing finish}
      {registeredLeft registeredRight leftInstall rightInstall installedLeft installedRight beforeLeft beforeRight activeLeft activeRight : Config (core3 grow) (HostState sig)}
      {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)} {body thread leftTicket rightTicket task callee tk args}
      (installed : SharedDestructorInstalled profile ready (specDispatch ready base) body leftTicket thread
        leftInstall installedLeft check)
      (canonical : SharedDestructorInstalled profile ready (specDispatch ready (LiveDispatch.host bindings base)) body rightTicket thread
        rightInstall installedRight canon)
      (resumed : SharedDestructorResumed profile ready (specDispatch ready base) body leftTicket thread beforeLeft activeLeft check)
      (peerResume : SharedDestructorResumed profile ready (specDispatch ready (LiveDispatch.host bindings base))
        body rightTicket thread beforeRight activeRight canon)
      (selected : body = sharedDestructorThread task callee)
      (workerSource : SharedDestructorRegisteredSource task registeredLeft.store registeredRight.store)
      (checkedPop : SharedDestructorOnStartPop profile ready (specDispatch ready base)
        ⟨some thread, [], check.control (sharedDestructorAfterResume body leftTicket)⟩
        tk.caller (sharedDestructorStartReply task callee tk) args reached)
      (canonicalPop : SharedDestructorOnStartPop profile ready (specDispatch ready (LiveDispatch.host bindings base))
        ⟨some thread, [], canon.control (sharedDestructorAfterResume body rightTicket)⟩
        tk.caller (sharedDestructorStartReply task callee tk) args peer)
      (tickets : leftTicket ≠ rightTicket)
      (ending : CallbackSliceEnd profile ready base bindings changes reached peer trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer trailing finish
  /-- The worker's actual Core import passed the common dispatcher reads.
  Its Core return occurrence remains parked over the two parent programs. -/
  | sharedDropWorkerImport {changes reached peer trailing finish}
      {thread frames peerFrames rest peerRest core host args task tk body}
      (parents : DestructorParentChain changes body rest peerRest)
      (segments : List.Forall₂ (ReturnFrame.Related.Segment changes) frames peerFrames)
      (admitted : calloutEntry reached.store thread host = none)
      (stores : reached.store = peer.store)
      (checked : reached.ctl = ⟨thread, .prog (calloutBody Limits.spec Quirks.none ready base reached.store thread host args),
        .core core (sharedDestructorCoreResult task tk) :: frames⟩ :: rest)
      (canonical : peer.ctl = ⟨thread, .prog (calloutBody Limits.spec Quirks.none ready (LiveDispatch.host bindings base)
        peer.store thread host args), .core core (sharedDestructorCoreResult task tk) :: peerFrames⟩ :: peerRest)
      (residual : Steps profile ready (specDispatch ready base) reached trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer trailing finish
  /-- The compiled shared record has passed both actual root prepares.
  Its recursive emitter is pending under the original continuations. -/
  | sharedDropRecordPrepared {changes reached peer trailing finish name kind inst ptr leftTicket rightTicket}
      {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
      {destination : RecordDestination} {tag : sig.Tag} {payload : Stored.OwnedMemory.Payload (sig.payload tag)}
      {fields : List Stored.Endpoints.RecordLower.Field} {objects : List Stored.Endpoints.RecordLower.Object}
      (parents : SourceParentStack changes check.rest canon.rest)
      (thread : check.thread = canon.thread)
      (segments : List.Forall₂ (ReturnFrame.Related.Segment changes) check.frames canon.frames)
      (linked : resolveBinding bindings name kind = .ok ⟨name, inst, .giveRecord destination⟩)
      (compiled : Stored.OwnedMemory.Claims.Record.preflight (destination.context (grow := grow) inst)
        (sig.payload tag) payload (.memory ptr) = .ok (fields, objects))
      (emitted : ∀ field ∈ fields, Stored.Endpoints.RecordLower.Field.Emitted field)
      (stores : reached.store = peer.store)
      (checkedPrepare : Stored.OwnedMemory.Claims.Record.prepare reached.store reached.host.writer
        (Stored.Endpoints.RecordLower.Field.listObjects fields) = .ok ())
      (canonicalPrepare : Stored.OwnedMemory.Claims.Record.prepare peer.store peer.host.writer
        (Stored.Endpoints.RecordLower.Field.listObjects fields) = .ok ())
      (checked : reached.ctl = check.control (sharedRecordEmit (destination.context inst) (sig.payload tag) payload.val.value fields ptr leftTicket))
      (canonical : peer.ctl = canon.control (sharedRecordEmit (destination.context inst) (sig.payload tag) payload.val.value fields ptr rightTicket))
      (ending : CallbackSliceEnd profile ready base bindings changes reached peer trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer trailing finish
  /-- The compiler's actual allocation instruction entered the canonical
  realloc body and parked its source-specific return segments. -/
  | sharedDropRecordAllocatorBody {changes left right reached peer trailing finish}
      {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)} {cx : LiftLowerContext (core3 grow)}
      {site : SharedRecordAllocation}
      {leftNext rightNext : Except Stored.Endpoints.RecordLower.Issue Unit → Session grow sig (Ret (core3 grow))}
      (parents : SourceParentStack changes check.rest canon.rest)
      (thread : check.thread = canon.thread)
      (segments : List.Forall₂ (ReturnFrame.Related.Segment changes) check.frames canon.frames)
      (compiled : site.compiled cx)
      (stores : reached.store = peer.store)
      (scheduler : DestructorSchedulerAlignment changes reached peer)
      (checked : left.ctl = check.control (.op (.call (site.call cx)) (site.resume cx leftNext)))
      (canonical : right.ctl = canon.control (.op (.call (site.call cx)) (site.resume cx rightNext)))
      (installed : Step profile ready (specDispatch ready base) left .tau reached)
      (peerInstalled : Step profile ready (specDispatch ready (LiveDispatch.host bindings base)) right .tau peer)
      (checkedBody : reached.ctl = (PayloadPrefix.Cursor.mk check.thread
          (.prog (site.resume cx leftNext) :: check.frames) check.rest).control (specDispatch ready base (site.call cx)))
      (canonicalBody : peer.ctl = (PayloadPrefix.Cursor.mk canon.thread
          (.prog (site.resume cx rightNext) :: canon.frames) canon.rest).control
        (specDispatch ready (LiveDispatch.host bindings base) (site.call cx)))
      (ending : CallbackSliceEnd profile ready base bindings changes reached peer trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer trailing finish
  /-- The actual allocator worker resumed. Its parent keeps the exact
  synchronous loop, caller lookup and original allocator return segment. -/
  | sharedDropRecordAllocatorResumed {changes left right reached peer trailing finish callee task caller worker}
      {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)} {cx : LiftLowerContext (core3 grow)}
      {request : ABI.ReallocRequest} {width : AddrType}
      (parents : SourceParentStack changes check.rest canon.rest)
      (thread : check.thread = canon.thread)
      (stores : reached.store = peer.store)
      (scheduler : DestructorSchedulerAlignment changes reached peer)
      (allocatorSource : SharedRecordAllocatorSource cx request width task caller reached.store)
      (workerSource : left.cont? worker =
        some (StepDefs.threadAct (specDispatch ready base) worker (.liftImplicit task callee)))
      (peerSource : right.cont? worker =
        some (StepDefs.threadAct (specDispatch ready (LiveDispatch.host bindings base)) worker (.liftImplicit task callee)))
      (checkedResume : Step profile ready (specDispatch ready base) left .tau reached)
      (canonicalResume : Step profile ready (specDispatch ready (LiveDispatch.host bindings base)) right .tau peer)
      (checkedAt : reached.ctl = StepDefs.threadAct (specDispatch ready base) worker (.liftImplicit task callee) ::
        check.control (sharedRecordAllocatorAfterResume cx task caller))
      (canonicalAt : peer.ctl = StepDefs.threadAct (specDispatch ready (LiveDispatch.host bindings base)) worker (.liftImplicit task callee) ::
        canon.control (sharedRecordAllocatorAfterResume cx task caller))
      (sourceParents : SourceParentStack changes (check.control (sharedRecordAllocatorAfterResume cx task caller))
        (canon.control (sharedRecordAllocatorAfterResume cx task caller)))
      (ending : CallbackSliceEnd profile ready base bindings changes reached peer trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer trailing finish
  /-- The reached allocator worker has executed its synchronous registration.
  Its source caller and task are retained for the following actual onStart. -/
  | sharedDropRecordAllocatorRegistered {changes reached peer trailing finish callee task caller worker}
      {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)} {cx : LiftLowerContext (core3 grow)}
      {request : ABI.ReallocRequest} {width : AddrType}
      (parents : SourceParentStack changes check.rest canon.rest)
      (thread : check.thread = canon.thread)
      (stores : reached.store = peer.store)
      (scheduler : DestructorSchedulerAlignment changes reached peer)
      (source : SharedRecordAllocatorSource cx request width task caller reached.store)
      (checked : reached.ctl = (PayloadPrefix.Cursor.mk (some worker) []
        (check.control (sharedRecordAllocatorAfterResume cx task caller))).control (sharedDestructorAfterAdmission task (some callee) true))
      (canonical : peer.ctl = (PayloadPrefix.Cursor.mk (some worker) []
        (canon.control (sharedRecordAllocatorAfterResume cx task caller))).control (sharedDestructorAfterAdmission task (some callee) true))
      (ending : CallbackSliceEnd profile ready base bindings changes reached peer trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer trailing finish
  /-- Both original onStart frames popped after reading the source allocator
  arguments. The actual Core argument lowering remains in the two workers. -/
  | sharedDropRecordAllocatorArguments {changes reached peer trailing finish callee task caller worker}
      {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)} {cx : LiftLowerContext (core3 grow)}
      {request : ABI.ReallocRequest} {width : AddrType} {entry : Task (core3 grow)}
      (parents : SourceParentStack changes check.rest canon.rest)
      (thread : check.thread = canon.thread)
      (stores : reached.store = peer.store)
      (scheduler : DestructorSchedulerAlignment changes reached peer)
      (source : SharedRecordAllocatorSource cx request width task caller reached.store)
      (typeAt : entry.ft = reallocType width)
      (optionsAt : entry.opts = {})
      (instanceAt : entry.inst = cx.inst)
      (callerAt : entry.caller = caller)
      (checkedPop : SharedLiftOnStartPop 2 profile ready (specDispatch ready base)
        ⟨some worker, [], check.control (sharedRecordAllocatorAfterResume cx task caller)⟩
        entry.caller (sharedDestructorStartReply task (some callee) entry) (sharedRecordAllocatorArgs width request) reached)
      (canonicalPop : SharedLiftOnStartPop 2 profile ready (specDispatch ready (LiveDispatch.host bindings base))
        ⟨some worker, [], canon.control (sharedRecordAllocatorAfterResume cx task caller)⟩
        entry.caller (sharedDestructorStartReply task (some callee) entry) (sharedRecordAllocatorArgs width request) peer)
      (checked : reached.ctl = (PayloadPrefix.Cursor.mk (some worker) []
        (check.control (sharedRecordAllocatorAfterResume cx task caller))).control
        (sharedDestructorArguments task (some callee) entry (sharedRecordAllocatorArgs width request)))
      (canonical : peer.ctl = (PayloadPrefix.Cursor.mk (some worker) []
        (canon.control (sharedRecordAllocatorAfterResume cx task caller))).control
        (sharedDestructorArguments task (some callee) entry (sharedRecordAllocatorArgs width request)))
      (ending : CallbackSliceEnd profile ready base bindings changes reached peer trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer trailing finish
  /-- The allocator's installed reentrant import passed the actual admission reads. -/
  | sharedDropRecordAllocatorCoreCallout {changes reached peer trailing finish task caller worker host args}
      {core : (core3 grow).Thread (CanonHost (core3 grow))} {entry : Task (core3 grow)}
      {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)} {cx : LiftLowerContext (core3 grow)}
      {request : ABI.ReallocRequest} {width : AddrType}
      (parents : SourceParentStack changes check.rest canon.rest)
      (thread : check.thread = canon.thread)
      (stores : reached.store = peer.store)
      (scheduler : DestructorSchedulerAlignment changes reached peer)
      (source : SharedRecordAllocatorSource cx request width task caller reached.store)
      (typeAt : entry.ft = reallocType width) (optionsAt : entry.opts = {}) (callerAt : entry.caller = caller)
      (checked : reached.ctl = ⟨some worker, .prog
        (calloutBody Limits.spec Quirks.none ready base reached.store (some worker) host args),
        [.core core (sharedDestructorCoreResult task entry)]⟩ ::
        check.control (sharedRecordAllocatorAfterResume cx task caller))
      (canonical : peer.ctl = ⟨some worker, .prog
        (calloutBody Limits.spec Quirks.none ready (LiveDispatch.host bindings base) peer.store (some worker) host args),
        [.core core (sharedDestructorCoreResult task entry)]⟩ ::
        canon.control (sharedRecordAllocatorAfterResume cx task caller))
      (admitted : calloutEntry reached.store (some worker) host = none)
      (residual : Steps profile ready (specDispatch ready base) reached trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer trailing finish
  /-- Both allocator Core activations returned the actual words to the
  canonical result lift. The original allocation return remains parked. -/
  | sharedDropRecordAllocatorCoreReturned {changes reached peer trailing finish task caller worker words}
      {entry : Task (core3 grow)}
      {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)} {cx : LiftLowerContext (core3 grow)}
      {request : ABI.ReallocRequest} {width : AddrType}
      (parents : SourceParentStack changes check.rest canon.rest)
      (thread : check.thread = canon.thread)
      (stores : reached.store = peer.store)
      (scheduler : DestructorSchedulerAlignment changes reached peer)
      (source : SharedRecordAllocatorSource cx request width task caller reached.store)
      (typeAt : entry.ft = reallocType width) (optionsAt : entry.opts = {}) (callerAt : entry.caller = caller)
      (checked : reached.ctl = (PayloadPrefix.Cursor.mk (some worker) []
        (check.control (sharedRecordAllocatorAfterResume cx task caller))).control (sharedDestructorCoreResult task entry words))
      (canonical : peer.ctl = (PayloadPrefix.Cursor.mk (some worker) []
        (canon.control (sharedRecordAllocatorAfterResume cx task caller))).control (sharedDestructorCoreResult task entry words))
      (ending : CallbackSliceEnd profile ready base bindings changes reached peer trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer trailing finish
  /-- Both allocator workers completed their actual onResolve pop. Their
  reached caller records hold the lifted result, and the task still has its
  original completion program before the resolved-state write. -/
  | sharedDropRecordAllocatorResolved {changes reached peer trailing finish task caller worker value}
      {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)} {cx : LiftLowerContext (core3 grow)}
      {request : ABI.ReallocRequest} {width : AddrType}
      (parents : SourceParentStack changes check.rest canon.rest)
      (thread : check.thread = canon.thread)
      (stores : reached.store = peer.store)
      (scheduler : DestructorSchedulerAlignment changes reached peer)
      (source : SharedRecordAllocatorSource cx request width task caller reached.store (some value))
      (checkedPop : SharedRecordAllocatorResolvePop profile ready (specDispatch ready base)
        ⟨some worker, [], check.control (sharedRecordAllocatorAfterResume cx task caller)⟩ task caller value reached)
      (canonicalPop : SharedRecordAllocatorResolvePop profile ready (specDispatch ready (LiveDispatch.host bindings base))
        ⟨some worker, [], canon.control (sharedRecordAllocatorAfterResume cx task caller)⟩ task caller value peer)
      (checked : reached.ctl = (PayloadPrefix.Cursor.mk (some worker) []
        (check.control (sharedRecordAllocatorAfterResume cx task caller))).control (sharedDestructorResolveReply task .unit))
      (canonical : peer.ctl = (PayloadPrefix.Cursor.mk (some worker) []
        (canon.control (sharedRecordAllocatorAfterResume cx task caller))).control (sharedDestructorResolveReply task .unit))
      (ending : CallbackSliceEnd profile ready base bindings changes reached peer trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer trailing finish
  /-- The allocator worker's actual exit exposed the two original parents.
  Their shared task has resolved and its caller retains the lifted pointer. -/
  | sharedDropRecordAllocatorWorkerExited {changes reached peer trailing finish task caller value}
      {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)} {cx : LiftLowerContext (core3 grow)}
      {request : ABI.ReallocRequest} {width : AddrType}
      (parents : SourceParentStack changes check.rest canon.rest)
      (thread : check.thread = canon.thread)
      (stores : reached.store = peer.store)
      (scheduler : DestructorSchedulerAlignment changes reached peer)
      (source : SharedRecordAllocatorSource cx request width task caller reached.store (some value))
      (resolved : ∃ tk, ArenaField.tasks.get? reached.store task = some tk ∧ tk.state = .resolved)
      (checked : reached.ctl = check.control (sharedRecordAllocatorAfterResume cx task caller))
      (canonical : peer.ctl = canon.control (sharedRecordAllocatorAfterResume cx task caller))
      (ending : CallbackSliceEnd profile ready base bindings changes reached peer trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer trailing finish
  /-- The actual synchronous loop popped after reading the resolved source
  task. The allocator return remains underneath the loop occurrence. -/
  | sharedDropRecordAllocatorLoopPopped {changes left right reached peer trailing finish task caller value}
      {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)} {cx : LiftLowerContext (core3 grow)}
      {request : ABI.ReallocRequest} {width : AddrType}
      (parents : SourceParentStack changes check.rest canon.rest)
      (thread : check.thread = canon.thread)
      (stores : reached.store = peer.store)
      (scheduler : DestructorSchedulerAlignment changes reached peer)
      (source : SharedRecordAllocatorSource cx request width task caller reached.store (some value))
      (checkedFocus : left.ctl = { check with frames := .prog (sharedRecordAllocatorLoopReply cx caller) :: check.frames }.control (.pure .unit))
      (canonicalFocus : right.ctl = { canon with frames := .prog (sharedRecordAllocatorLoopReply cx caller) :: canon.frames }.control (.pure .unit))
      (checkedPop : Step profile ready (specDispatch ready base) left .tau reached)
      (canonicalPop : Step profile ready (specDispatch ready (LiveDispatch.host bindings base)) right .tau peer)
      (checked : reached.ctl = check.control (sharedRecordAllocatorResult cx caller))
      (canonical : peer.ctl = canon.control (sharedRecordAllocatorResult cx caller))
      (ending : CallbackSliceEnd profile ready base bindings changes reached peer trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer trailing finish
  /-- The actual caller-result lookup reached a pointer return. The
  allocator return segment is still parked at this finite cut. -/
  | sharedDropRecordAllocatorReturning {changes reached peer trailing finish caller args kind n}
      {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
      (parents : SourceParentStack changes check.rest canon.rest)
      (thread : check.thread = canon.thread)
      (stores : reached.store = peer.store)
      (scheduler : DestructorSchedulerAlignment changes reached peer)
      (lookup : ArenaField.callers.get? reached.store caller = some (.sub (.realloc args (some (.int kind n)))))
      (checked : reached.ctl = check.control (.pure (.nat n.toNat)))
      (canonical : peer.ctl = canon.control (.pure (.nat n.toNat)))
      (ending : CallbackSliceEnd profile ready base bindings changes reached peer trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer trailing finish
  /-- Both source allocator return occurrences popped, exposing the compiled
  visitor resumes with the pointer read from the original allocator caller. -/
  | sharedDropRecordAllocatorPopped {changes left right reached peer trailing finish pointer}
      {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
      {first second : ReturnFrame.Continuation (core3 grow) (HostState sig)}
      (source : SourceAllocatorReturn first second)
      (parents : SourceParentStack changes check.rest canon.rest)
      (stores : reached.store = peer.store)
      (scheduler : DestructorSchedulerAlignment changes reached peer)
      (checkedFocus : left.ctl = { check with frames := .prog first :: check.frames }.control (.pure (.nat pointer)))
      (canonicalFocus : right.ctl = { canon with frames := .prog second :: canon.frames }.control (.pure (.nat pointer)))
      (checkedPop : Step profile ready (specDispatch ready base) left .tau reached)
      (canonicalPop : Step profile ready (specDispatch ready (LiveDispatch.host bindings base)) right .tau peer)
      (checkedLost : ReturnFrame.Occurrence.Trail profile ready (specDispatch ready base) left (some (.active 0 0)) [.tau] reached none)
      (canonicalLost : ReturnFrame.Occurrence.Trail profile ready (specDispatch ready (LiveDispatch.host bindings base))
        right (some (.active 0 0)) [.tau] peer none)
      (checked : reached.ctl = check.control (first (.nat pointer)))
      (canonical : peer.ctl = canon.control (second (.nat pointer)))
      (ending : CallbackSliceEnd profile ready base bindings changes reached peer trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer trailing finish
  /-- The actual nested worker is running above two separate source parent
  programs and the enclosing dormant parents. -/
  | sharedDropNestedResumed {changes reached peer trailing finish impl task leftTicket rightTicket worker beforeLeft beforeRight}
      {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
      {request : InstId × DtorRequest (core3 grow)}
      (parents : SourceParentStack changes check.rest canon.rest)
      (thread : check.thread = canon.thread)
      (segments : List.Forall₂ (ReturnFrame.Related.Segment changes) check.frames canon.frames)
      (implementation : request.2.impl = some impl)
      (stores : reached.store = peer.store)
      (scheduler : DestructorSchedulerAlignment changes reached peer)
      (checked : SharedDestructorResumed profile ready (specDispatch ready base) (sharedDestructorThread task request.2.dtor)
        leftTicket worker beforeLeft reached check)
      (canonical : SharedDestructorResumed profile ready (specDispatch ready (LiveDispatch.host bindings base))
        (sharedDestructorThread task request.2.dtor) rightTicket worker beforeRight peer canon)
      (sourceParents : SourceParentStack changes (check.control (sharedDestructorAfterResume (sharedDestructorThread task request.2.dtor) leftTicket))
        (canon.control (sharedDestructorAfterResume (sharedDestructorThread task request.2.dtor) rightTicket)))
      (ending : CallbackSliceEnd profile ready base bindings changes reached peer trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer trailing finish
  /-- The actual nested worker entered and registered under its source
  parent stack. Its onStart body uses the reached task and caller records. -/
  | sharedDropNestedRegistered {changes reached peer trailing finish task callee}
      {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
      (parents : SourceParentStack changes check.rest canon.rest)
      (source : SharedDestructorRegisteredSource task reached.store peer.store)
      (scheduler : DestructorSchedulerAlignment changes reached peer)
      (checked : reached.ctl = check.control (sharedDestructorAfterAdmission task callee true))
      (canonical : peer.ctl = canon.control (sharedDestructorAfterAdmission task callee true))
      (ending : CallbackSliceEnd profile ready base bindings changes reached peer trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer trailing finish
  /-- A nested destructor Core worker passed the actual import admission
  checks under its own heterogeneous source parent stack. -/
  | sharedDropNestedCoreCallout {changes reached peer trailing finish task entry core host args worker}
      {leftRest rightRest}
      (parents : SourceParentStack changes leftRest rightRest)
      (stores : reached.store = peer.store)
      (scheduler : DestructorSchedulerAlignment changes reached peer)
      (source : SharedDestructorTaskSource task reached.store)
      (checked : reached.ctl = ⟨some worker, .prog
        (calloutBody Limits.spec Quirks.none ready base reached.store (some worker) host args),
        [.core core (sharedDestructorCoreResult task entry)]⟩ :: leftRest)
      (canonical : peer.ctl = ⟨some worker, .prog
        (calloutBody Limits.spec Quirks.none ready (LiveDispatch.host bindings base) peer.store (some worker) host args),
        [.core core (sharedDestructorCoreResult task entry)]⟩ :: rightRest)
      (admitted : calloutEntry reached.store (some worker) host = none)
      (residual : Steps profile ready (specDispatch ready base) reached trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer trailing finish
  /-- The source switch reached its actual scheduler instruction after the
  target checks. The target slot is read after saving the current worker. -/
  | sharedDropSwitch {changes reached peer trailing finish body worker target frames peerFrames rest peerRest reply}
      (parents : DestructorParentChain changes body rest peerRest)
      (segments : List.Forall₂ (ReturnFrame.Related.Segment changes) frames peerFrames)
      (stores : reached.store = peer.store)
      (checked : reached.ctl = (PayloadPrefix.Cursor.mk (some worker) frames rest).control
        (.op (.block (some target)) fun _ => reply))
      (canonical : peer.ctl = (PayloadPrefix.Cursor.mk (some worker) peerFrames peerRest).control
        (.op (.block (some target)) fun _ => reply))
      (residual : Steps profile ready (specDispatch ready base) reached trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer trailing finish
  /-- The reached activation and its resumers run above a dormant
  source parent stack. The checked suffix starts at this actual scheduler state. -/
  | sharedDropSwitchTarget {changes reached peer trailing finish left right active peerActive rest peerRest}
      (parents : SourceParentStack changes rest peerRest)
      (target : ReturnFrame.Related.Active changes left right)
      (resumers : List.Forall₂ (ReturnFrame.Related.Active changes) active peerActive)
      (stores : reached.store = peer.store)
      (scheduler : DestructorSchedulerAlignment changes reached peer)
      (checked : reached.ctl = left :: (active ++ rest))
      (canonical : peer.ctl = right :: (peerActive ++ peerRest))
      (residual : Steps profile ready (specDispatch ready base) reached trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer trailing finish
  /-- A source worker prefix preserving scheduler data through actual steps. -/
  | destructorPrefix {changes reached peer left right leading live trailing finish marks}
      (paths : OccurrenceTransport profile ready base bindings reached peer leading live left right marks)
      (writers : VisitorWriterPath profile ready base bindings reached peer leading live left right)
      (scheduler : DestructorSchedulerAlignment changes reached peer → DestructorSchedulerAlignment changes left right)
      (ending : CallbackSliceEnd profile ready base bindings changes left right trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer (leading ++ trailing) finish
  /-- The enclosing return occurrence is lost at the executed parent pop.
  The checked suffix starts at the actual endpoint of that instruction. -/
  | sharedDropParentPop {changes reached peer left right trailing finish}
      (paths : OccurrenceTransport profile ready base bindings reached peer [.tau] [.tau] left right)
      (writers : VisitorWriterPath profile ready base bindings reached peer [.tau] [.tau] left right)
      (checkedLost : ReturnFrame.Occurrence.Trail profile ready (specDispatch ready base) reached (some (.active 0 0)) [.tau] left none)
      (canonicalLost : ReturnFrame.Occurrence.Trail profile ready (specDispatch ready (LiveDispatch.host bindings base))
        peer (some (.active 0 0)) [.tau] right none)
      (restore : DestructorSchedulerAlignment changes reached peer → HostFrame.Related.Paired changes left right)
      (residual : Steps profile ready (specDispatch ready base) left trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer (.tau :: trailing) finish
  /-- The actual paired enclosing pop hands the checked suffix to the mixed
induction. Its trails still identify the removed original occurrences. -/
  | sharedDropParentJoined {changes reached peer left right trailing finish}
      (paths : OccurrenceTransport profile ready base bindings reached peer [.tau] [.tau] left right)
      (writers : VisitorWriterPath profile ready base bindings reached peer [.tau] [.tau] left right)
      (checkedLost : ReturnFrame.Occurrence.Trail profile ready (specDispatch ready base) reached (some (.active 0 0)) [.tau] left none)
      (canonicalLost : ReturnFrame.Occurrence.Trail profile ready (specDispatch ready (LiveDispatch.host bindings base))
        peer (some (.active 0 0)) [.tau] right none)
      (restored : HostFrame.Related.Paired changes left right)
      (ending : CallbackSliceEnd profile ready base bindings changes left right trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer (.tau :: trailing) finish
  /-- A parked worker exposed the original parents. Their actual loop call
  installs the two source continuations before the shorter scheduler run. -/
  | sharedDropParentLoop {changes reached peer left right trailing finish leftTicket rightTicket enclosing}
      (paths : OccurrenceTransport profile ready base bindings reached peer [.tau] [.tau] left right [some (.active 0 0)])
      (writers : VisitorWriterPath profile ready base bindings reached peer [.tau] [.tau] left right)
      (frames : DestructorParentLoopFrames (sharedDestructorParentReply leftTicket) (sharedDestructorParentReply rightTicket)
        enclosing left right)
      (restore : DestructorSchedulerAlignment changes reached peer →
        HostFrame.Related.Paired (ReturnFrame.Extend changes (sharedDestructorParentReply leftTicket)
          (sharedDestructorParentReply rightTicket)) left right ∧
        ReturnFrame.Occurrence.Outside changes (ReturnFrame.Occurrence.segmentStorage left)
          (ReturnFrame.Occurrence.segmentStorage right) (some (.active 0 0)))
      (residual : Steps profile ready (specDispatch ready base) left trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer (.tau :: trailing) finish
  /-- Compare the reached loop under its installed return substitution. Both
  original occurrences are present when this comparison starts. -/
  | sharedDropParentLoopJoined {changes reached peer trailing finish first second enclosing}
      (frames : DestructorParentLoopFrames first second enclosing reached peer)
      (restored : HostFrame.Related.Paired (ReturnFrame.Extend changes first second) reached peer)
      (outside : ReturnFrame.Occurrence.Outside changes
        (ReturnFrame.Occurrence.segmentStorage reached)
        (ReturnFrame.Occurrence.segmentStorage peer) (some (.active 0 0)))
      (ending : CallbackSliceEnd profile ready base bindings (ReturnFrame.Extend changes first second)
        reached peer trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer trailing finish
  /-- The executed original loop pop removes only the loop substitution.
  The enclosing occurrence remains active for its ticket-specific journal. -/
  | sharedDropLoopReturn {changes reached peer left right trailing finish first second checkEntry canonEntry checkTrace canonTrace}
      (paths : OccurrenceTransport profile ready base bindings reached peer [.tau] [.tau] left right)
      (writers : VisitorWriterPath profile ready base bindings reached peer [.tau] [.tau] left right)
      (checkedLost : ReturnFrame.Occurrence.Trail profile ready (specDispatch ready base) reached (some (.active 0 0)) [.tau] left none)
      (canonicalLost : ReturnFrame.Occurrence.Trail profile ready (specDispatch ready (LiveDispatch.host bindings base))
        peer (some (.active 0 0)) [.tau] right none)
      (checkedEnclosing : ReturnFrame.Occurrence.Trail profile ready (specDispatch ready base)
        checkEntry (some (.active 0 1)) (checkTrace ++ [.tau]) left (some (.active 0 0)))
      (canonicalEnclosing : ReturnFrame.Occurrence.Trail profile ready (specDispatch ready (LiveDispatch.host bindings base))
        canonEntry (some (.active 0 1)) (canonTrace ++ [.tau]) right (some (.active 0 0)))
      (ending : CallbackSliceEnd profile ready base bindings changes left right trailing finish) :
      CallbackSliceEnd profile ready base bindings (ReturnFrame.Extend changes first second) reached peer (.tau :: trailing) finish
  | sharedDropCompared {changes reached peer left right workerLeft workerRight entered checked canonical trailing finish marks}
      {beforeLeft beforeRight : Config (core3 grow) (HostState sig)}
      {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)} {body thread ticket}
      (resumed : SharedDestructorResumed profile ready (specDispatch ready base) body ticket thread beforeLeft workerLeft check)
      (peerResume : SharedDestructorResumed profile ready (specDispatch ready (LiveDispatch.host bindings base))
        body ticket thread beforeRight workerRight canon)
      (paths : OccurrenceTransport profile ready base bindings reached peer entered entered workerLeft workerRight marks)
      (writers : VisitorWriterPath profile ready base bindings reached peer entered entered workerLeft workerRight)
      (compared : ExecutedCallbackSegment profile ready base bindings changes workerLeft workerRight checked canonical left right)
      (ending : CallbackSliceEnd profile ready base bindings changes left right trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer (entered ++ (checked ++ trailing)) finish
  | sharedGiveProbeMismatch {changes reached peer left right leading trailing finish marks}
      {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
      {name kind inst leftTicket rightTicket position claim beforeLeft beforeRight}
      {action : SharedGiveAction} {tree : Stored.OwnedMemory.Tree sig}
      (linked : resolveBinding bindings name kind = .ok ⟨name, inst, action.bindingAction⟩)
      (source : action.claimAt tree position = some claim)
      (site : SharedGiveProbeMismatch claim inst leftTicket rightTicket beforeLeft beforeRight left right check canon)
      (paths : OccurrenceTransport profile ready base bindings reached peer leading leading left right marks)
      (writers : VisitorWriterPath profile ready base bindings reached peer leading leading left right)
      (residual : Steps profile ready (specDispatch ready base) left trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer (leading ++ trailing) finish
  | sharedGiveSelectionMismatch {changes reached peer left right leading trailing finish marks}
      {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
      {inst leftTicket rightTicket position handle beforeLeft beforeRight} {action : SharedGiveAction}
      (mismatch : SharedGiveHistoryMismatch action inst leftTicket rightTicket position handle beforeLeft beforeRight left right check canon)
      (checked : ReachedReadOccurrences profile ready (specDispatch ready base) reached beforeLeft left leading)
      (canonical : ReachedReadOccurrences profile ready (specDispatch ready (LiveDispatch.host bindings base))
        peer beforeRight right leading)
      (paths : OccurrenceTransport profile ready base bindings reached peer (leading ++ [.tau]) (leading ++ [.tau]) left right marks)
      (writers : VisitorWriterPath profile ready base bindings reached peer (leading ++ [.tau]) (leading ++ [.tau]) left right)
      (residual : Steps profile ready (specDispatch ready base) left trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer ((leading ++ [.tau]) ++ trailing) finish
  | componentEntryPrefix {changes wider reached peer left right labels mark}
      {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
      (site : PairedComponentSite wider left right check canon)
      (checked : ∃ program, left.ctl = check.control program)
      (canonical : ∃ program, right.ctl = canon.control program)
      (paths : OccurrenceTransport profile ready base bindings reached peer labels labels left right [mark])
      (writers : VisitorWriterPath profile ready base bindings reached peer labels labels left right) :
      CallbackSliceEnd profile ready base bindings changes reached peer labels left
  | componentObserverTerminal {changes wider reached peer left right leading trailing finish mark}
      {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
      (terminal : (trailing = [] ∧ PairedComponentSite wider left right check canon) ∨
        (left.ctl = [] ∧ right.ctl = [] ∧ HostFrame.Related.Paired wider left right))
      (paths : OccurrenceTransport profile ready base bindings reached peer leading leading left right [mark])
      (writers : VisitorWriterPath profile ready base bindings reached peer leading leading left right)
      (residual : Steps profile ready (specDispatch ready base) left trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer (leading ++ trailing) finish
  | componentPreflightMismatch {changes reached peer left right leading trailing finish mark}
      {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)} {callee : ComponentCall.Callee sig}
      {caller leftTicket rightTicket leftPlan rightPlan}
      (checked : left.ctl = check.control (ComponentCall.acceptPlanned callee caller leftTicket leftPlan))
      (canonical : right.ctl = canon.control (ComponentCall.acceptPlanned callee caller rightTicket rightPlan))
      (different : leftPlan ≠ rightPlan)
      (history : reached.host.writer.accepted ≠ peer.host.writer.accepted)
      (paths : OccurrenceTransport profile ready base bindings reached peer leading leading left right [mark])
      (writers : VisitorWriterPath profile ready base bindings reached peer leading leading left right)
      (residual : Steps profile ready (specDispatch ready base) left trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer (leading ++ trailing) finish
  | componentRefusedTerminal {changes wider reached peer left right leading trailing finish mark}
      {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
      (frontier : ComponentStoreFrontier (Result := Unit) wider check canon
        (fun _ => .pure (.cancel .none)) (fun _ => .pure (.cancel .none)) left right trailing True)
      (terminal : trailing = [] ∨ (left.ctl = [] ∧ right.ctl = []))
      (paths : OccurrenceTransport profile ready base bindings reached peer leading leading left right [mark])
      (writers : VisitorWriterPath profile ready base bindings reached peer leading leading left right)
      (residual : Steps profile ready (specDispatch ready base) left trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer (leading ++ trailing) finish
  | componentRegistrationMismatch {changes wider reached peer left right leading trailing finish mark}
      {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)} {leftTicket rightTicket caller tree}
      (mismatch : ReachedRegistrationMismatch profile ready base bindings left right check canon leftTicket rightTicket caller tree)
      (site : PairedComponentSite wider left right check canon)
      (paths : OccurrenceTransport profile ready base bindings reached peer leading leading left right [mark])
      (writerPath : VisitorWriterPath profile ready base bindings reached peer leading leading left right)
      (writers : left.host.writer = reached.host.writer ∧ right.host.writer = peer.host.writer)
      (residual : Steps profile ready (specDispatch ready base) left trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer (leading ++ trailing) finish
  | componentAcceptedTerminal {changes wider reached peer left right leading trailing finish mark tree handle}
      {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
      (frontier : ComponentAcceptedFrontier wider check canon tree handle left right trailing)
      (terminal : trailing = [] ∨ (left.ctl = [] ∧ right.ctl = []))
      (paths : OccurrenceTransport profile ready base bindings reached peer leading leading left right [mark])
      (writers : VisitorWriterPath profile ready base bindings reached peer leading leading left right)
      (writerFlow : ∀ pending, reached.host.writer.ClaimDiscrepancies peer.host.writer pending →
        left.host.writer.ClaimDiscrepancies right.host.writer pending)
      (residual : Steps profile ready (specDispatch ready base) left trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer (leading ++ trailing) finish
  | componentReplyDisplaced {changes reached peer left right bodyEntry peerEntry bodyTrace leading trailing finish mark}
      {check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
      (tracked : AllocatorMark profile ready base bindings changes bodyEntry peerEntry bodyTrace bodyTrace left right mark)
      (focus : left.ctl = check.control (.pure (.cancel .none)))
      (missing : mark ≠ some (.active 0 0))
      (paths : OccurrenceTransport profile ready base bindings reached peer leading leading left right)
      (writers : VisitorWriterPath profile ready base bindings reached peer leading leading left right)
      (residual : Steps profile ready (specDispatch ready base) left trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer (leading ++ trailing) finish
  | refused {changes reached peer label next route destination ticket issue left right checkLeading canonLeading trailing finish marks}
      (install : GiveInstall bindings (specDispatch ready base) reached label next)
      (observed : PayloadPrefix.visible canonLeading = PayloadPrefix.visible checkLeading)
      (paths : OccurrenceTransport profile ready base bindings reached peer checkLeading canonLeading left right marks)
      (writers : VisitorWriterPath profile ready base bindings reached peer checkLeading canonLeading left right)
      (reply : CheckedOnlyGiveReply profile ready base bindings route destination ticket issue reached peer left right
        checkLeading canonLeading trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer (checkLeading ++ trailing) finish
  | directGiveTrap {changes reached peer left right checked canonical trailing finish reason}
      (cut : GiveBodyCut profile ready base bindings reached peer left right checked canonical trailing finish [none])
      (trapped : PayloadPrefix.visible checked = [.trap reason])
      (checkedLocked : left.ctl = []) (canonicalLocked : right.ctl = []) :
      CallbackSliceEnd profile ready base bindings changes reached peer (checked ++ trailing) finish
  | giveLookupMismatch {changes reached peer beforeLeft beforeRight left right checked canonical trailing finish handle marks}
      {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)} {checkNext canonNext}
      (request : GiveSelector bindings)
      (cut : GiveBodyCut profile ready base bindings reached peer left right checked canonical trailing finish marks)
      (checkedFocus : beforeLeft.ctl = check.control (select handle >>= checkNext))
      (canonicalFocus : beforeRight.ctl = canon.control (select handle >>= canonNext))
      (checkedRead : Step profile ready (specDispatch ready base) beforeLeft .tau left)
      (canonicalRead : Step profile ready (specDispatch ready (LiveDispatch.host bindings base)) beforeRight .tau right)
      (demand : request.lookupDemand beforeLeft.store check.thread = some handle)
      (different : Stored.Endpoints.Core.childFromHistory beforeLeft.host.writer.accepted handle ≠
        Stored.Endpoints.Core.childFromHistory beforeRight.host.writer.accepted handle) :
      CallbackSliceEnd profile ready base bindings changes reached peer (checked ++ trailing) finish
  /-- A checked-only root stop actually popped or locked down the original
  marked occurrence. The raw program remains at its reached pending control. -/
  | sourceOverlayCheckedTerminal {changes reached peer next label trailing finish}
      (step : Step profile ready (specDispatch ready base) reached label next)
      (edit : ReturnFrame.Occurrence.transitionEdit reached label = .pop ∨
        ReturnFrame.Occurrence.transitionEdit reached label = .clear)
      (writer : next.host.writer = reached.host.writer)
      (lost : ReturnFrame.Occurrence.Trail profile ready (specDispatch ready base) reached
        (some (.active 0 0)) [label] next none)
      (residual : Steps profile ready (specDispatch ready base) next trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer (label :: trailing) finish
  /-- Range validation and fresh checked reserve succeeded. The reached
  memory width differs from the width used to allocate and place these elements.
  Both element programs retain their actual controls. -/
  | sourceOverlayCollectionLayoutChanged {changes reached peer trailing finish pointer bytes}
      {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
      (destination : RecordDestination) (inst : InstId) (type element : Stored.TypeOf)
      (entries : List Stored.Endpoints.RecordLower.Field) (index : Nat) (output : Stored.Lower.Output)
      (checkNext : Except Stored.Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
      (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
      (parents : SourceParentStack changes check.rest canon.rest)
      (thread : check.thread = canon.thread)
      (segments : List.Forall₂ (ReturnFrame.Related.Segment changes) check.frames canon.frames)
      (matching : Stored.Endpoints.RecordLower.Field.EntriesMatch entries element)
      (source : SourceOverlayFieldSource destination (.dynamic type element entries))
      (aligned : pointer = ABI.alignTo pointer (ABI.layout destination.width element).alignment)
      (bounds : pointer + entries.length * (ABI.layout destination.width element).size ≤ bytes)
      (sized : (core3 grow).memSize? reached.store.core destination.memory = some bytes)
      (widthChanged : (core3 grow).memAddrType? reached.store.core destination.memory ≠ some destination.width)
      (stores : reached.store = peer.store)
      (scheduler : DestructorSchedulerAlignment changes reached peer)
      (checked : let area := ABI.layout destination.width element
        reached.ctl = check.control (PayloadPrefix.checkedCollectionTail destination inst entries area index output pointer (.ok ()) >>= checkNext))
      (canonical : let area := ABI.layout destination.width element
        let mode := Stored.Endpoints.RecordLower.CanonicalTree.EntryMode.forOutput destination.width type output
        peer.ctl = canon.control (PayloadPrefix.canonicalCollectionTail destination inst entries area output pointer mode >>= canonNext))
      (residual : Steps profile ready (specDispatch ready base) reached trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer trailing finish
  /-- Publication reached the two enclosing source controls. -/
  | sourceOverlayPublished {changes reached peer trailing finish continuation}
      (publication : ReachedSourcePublication continuation changes reached peer)
      (residual : Steps profile ready (specDispatch ready base) reached trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer trailing finish
  /-- A reached update on the path to publication fails the growth relation
  required by the enclosing visitor. The update and actual residual remain available. -/
  | sourceOverlayNonGrowing {changes reached peer trailing finish continuation leading}
      (publication : ReachedSourcePublication continuation changes reached peer)
      (update : ReachedNonGrowingUpdate profile ready (specDispatch ready base) continuation.entry leading reached)
      (residual : Steps profile ready (specDispatch ready base) reached trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer trailing finish
  | directGiveSelected {changes reached peer left right checked canonical trailing finish resume ticket}
      {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
      (request : GiveSelector bindings) (selected : SelectionValue sig request.schema)
      (cut : GiveBodyCut profile ready base bindings reached peer left right checked canonical trailing finish [some (.active 0 0)])
      (admission : request.Admitted left check.thread selected)
      (site : PairedComponentSite changes left right
        { check with frames := .prog resume :: check.frames } { canon with frames := .prog resume :: canon.frames })
      (checkedFocus : left.ctl = { check with frames := .prog resume :: check.frames }.control
        (request.checkedContinuation left.store check.thread (ticket, .ok selected)))
      (canonicalFocus : right.ctl = { canon with frames := .prog resume :: canon.frames }.control
        (referenceTail request.inst request.destination request.schema (.ok selected) >>= fun reply => pure (.flat reply)))
      (compiler : (∃ field plan, request.preflight (grow := grow) selected = .ok (field, plan) ∧
          left.ctl = { check with frames := .prog resume :: check.frames }.control
            (request.compiledContinuation ticket selected field plan) ∧
          DirectGivePreparationCut profile ready base bindings left right check resume request ticket selected field trailing finish) ∨
        ∃ issue, request.preflight (grow := grow) selected = .error issue ∧
          CheckedProgramReplyCut profile ready (specDispatch ready base) left check resume
            (giveAdmissionReply ticket request.destination request.schema (.lowerPayload issue)) trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer (checked ++ trailing) finish
  | compilerRefused {changes reached peer label next count canonLabels entered issue trailing finish route}
      {request : CoreGiveRequest bindings reached} (selection : request.Selected route)
      (install : GiveInstall bindings (specDispatch ready base) reached label next)
      (refused : selection.preflight = .error issue)
      (checked : ∀ place : ReturnFrame.Occurrence.Location,
        ReturnFrame.Occurrence.Trail profile ready (specDispatch ready base) reached (some place)
          (List.replicate count .tau) (selection.compilerRefused issue) (some place))
      (canonical : ∀ place : ReturnFrame.Occurrence.Location,
        ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base)) peer place canonLabels entered
          (((ReturnFrame.Occurrence.Edit.push (.core request.core request.next)).follow place).getD place))
      (quiet : PayloadPrefix.visible canonLabels = [])
      (pending : HostFrame.Related.Paired changes selection.canonicalPending entered)
      (host : entered.host = peer.host)
      (residual : Steps profile ready (specDispatch ready base) (selection.compilerRefused issue) trailing finish)
      (writerCut : ∃ used rest left, List.replicate count .tau ++ trailing = used ++ rest ∧
        GiveBodyCut profile ready base bindings reached peer left entered used canonLabels rest finish [some (.active 0 0)] ∧
        CheckedTerminalWriterTail profile ready (specDispatch ready base) left rest finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer (List.replicate count .tau ++ trailing) finish
  | placementTrap {changes peer label next count canonLabels entered reason trailing finish route}
      (site : PayloadRoot.Site grow sig route)
      (install : GiveInstall bindings (specDispatch ready base) site.start label next)
      (failed : PayloadPrefix.rootPlacement site.destination site.start.store (sig.payload site.tag) route.output = .error reason)
      (checked : site.EntryTrap profile ready base (List.replicate count .tau ++ [.trap reason]))
      (canonical : ∀ place : ReturnFrame.Occurrence.Location,
        ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base)) peer place canonLabels entered
          (site.entryPlace place))
      (quiet : PayloadPrefix.visible canonLabels = [])
      (pending : HostFrame.Related.Paired changes (site.reference site.referenceReply) entered)
      (host : entered.host = peer.host)
      (residual : Steps profile ready (specDispatch ready base) (StepDefs.trapCfg site.checked) trailing finish)
      (writerCut : ∃ used rest left, (List.replicate count .tau ++ [.trap reason]) ++ trailing = used ++ rest ∧
        GiveBodyCut profile ready base bindings site.start peer left entered used canonLabels rest finish [some (.active 0 0)] ∧
        CheckedTerminalWriterTail profile ready (specDispatch ready base) left rest finish) :
      CallbackSliceEnd profile ready base bindings changes site.start peer ((List.replicate count .tau ++ [.trap reason]) ++ trailing) finish
  | body {changes reached peer label next left right checked canonical trailing finish marks caller}
      (install : GiveInstall bindings (specDispatch ready base) reached label next)
      (cut : GiveBodyCut profile ready base bindings reached peer left right checked canonical trailing finish (marks ++ [caller]))
      (stop : GiveBodyStop profile ready base left right trailing finish caller) :
      CallbackSliceEnd profile ready base bindings changes reached peer (checked ++ trailing) finish
  | directGiveLateReply {changes reached peer left right checked canonical trailing finish resume}
      {caller : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
      (issue : Stored.Endpoints.RecordLower.Issue) (reply : Event × List FlatValue)
      (cut : GiveBodyCut profile ready base bindings reached peer left right checked canonical trailing finish [some (.active 0 0)])
      (focus : left.ctl = { caller with frames := .prog resume :: caller.frames }.control
        (do return .flat (← writeCompletion reply)))
      (replyCut : CheckedProgramReplyCut profile ready (specDispatch ready base) left caller resume reply trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer (checked ++ trailing) finish
  | directGiveFinite {changes reached peer right checked canonical finish marks}
      (cut : GiveBodyCut profile ready base bindings reached peer finish right checked canonical [] finish marks) :
      CallbackSliceEnd profile ready base bindings changes reached peer checked finish
  | allocator {changes reached peer label next left right checked canonical trailing finish caller
      checkEntry canonEntry checkLabels canonLabels mark first second}
      (install : GiveInstall bindings (specDispatch ready base) reached label next)
      (cut : GiveBodyCut profile ready base bindings reached peer left right checked canonical trailing finish [mark, caller])
      (tracked : AllocatorMark profile ready base bindings changes checkEntry canonEntry checkLabels canonLabels left right mark)
      (paired : HostFrame.Related.Paired (ReturnFrame.Extend changes first second) left right)
      (ending : CallbackSliceEnd profile ready base bindings (ReturnFrame.Extend changes first second) left right trailing finish)
      (notPopped : trailing = [] ∨ mark ≠ some (.active 0 0) ∨ ¬ ∃ (pointer : Nat)
        (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)),
        left.ctl = { cursor with frames := .prog first :: cursor.frames }.control (.pure (.nat pointer))) :
      CallbackSliceEnd profile ready base bindings changes reached peer (checked ++ trailing) finish
  | nonGrowing {changes reached peer left right checked canonical trailing finish marks}
      (update : ReachedNonGrowingUpdate profile ready (specDispatch ready base) reached checked left)
      (paired : HostFrame.Related.Paired changes left right)
      (paths : OccurrenceTransport profile ready base bindings reached peer checked canonical left right marks)
      (writers : VisitorWriterPath profile ready base bindings reached peer checked canonical left right)
      (residual : Steps profile ready (specDispatch ready base) left trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer (checked ++ trailing) finish
  | pollTerminal {changes reached peer left right checked trailing finish mark check canon}
      (paths : OccurrenceTransport profile ready base bindings reached peer checked checked left right [mark])
      (writerPath : VisitorWriterPath profile ready base bindings reached peer checked checked left right)
      (writers : CheckedSpendFlow reached.host.writer peer.host.writer left.host.writer right.host.writer [])
      (frontier : ComponentStoreFrontier changes check canon waitableFlatReply waitableFlatReply left right trailing True)
      (terminal : trailing = [] ∨ (left.ctl = [] ∧ right.ctl = []))
      (residual : Steps profile ready (specDispatch ready base) left trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer (checked ++ trailing) finish
  | waitTerminal {changes reached peer left right checked trailing finish check canon marks} {Result : Type}
      {next : Result → Session grow sig (Ret (core3 grow))}
      (paths : OccurrenceTransport profile ready base bindings reached peer checked checked left right marks)
      (writerPath : VisitorWriterPath profile ready base bindings reached peer checked checked left right)
      (frontier : ComponentStoreFrontier changes check canon next next left right trailing True)
      (terminal : trailing = [] ∨ (left.ctl = [] ∧ right.ctl = []))
      (residual : Steps profile ready (specDispatch ready base) left trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer (checked ++ trailing) finish
  | cancelTerminal {changes reached peer left right checked canonical trailing finish marks}
      (paths : OccurrenceTransport profile ready base bindings reached peer checked canonical left right marks)
      (writerPath : VisitorWriterPath profile ready base bindings reached peer checked canonical left right)
      (observed : PayloadPrefix.visible canonical = PayloadPrefix.visible checked)
      (exit : CancelFinishExit profile ready base bindings changes left right trailing finish)
      (terminal : trailing = [] ∨ (left.ctl = [] ∧ right.ctl = []))
      (residual : Steps profile ready (specDispatch ready base) left trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer (checked ++ trailing) finish
  | cancelHookBody {changes reached peer left right entry peerEntry checked canonical hookChecked hookCanonical trailing
        finish mark marks resume}
      (paths : OccurrenceTransport profile ready base bindings reached peer checked canonical left right marks)
      (writers : VisitorWriterPath profile ready base bindings reached peer checked canonical left right)
      (observed : PayloadPrefix.visible checked = PayloadPrefix.visible canonical)
      (hook : AllocatorMark profile ready base bindings changes entry peerEntry hookChecked hookCanonical left right mark)
      (ending : CallbackSliceEnd profile ready base bindings (ReturnFrame.Extend changes resume resume) left right trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer (checked ++ trailing) finish
  | cancelDecisionTerminal {changes reached peer left right checked canonical trailing finish check canon subtask marks}
      (paths : OccurrenceTransport profile ready base bindings reached peer checked canonical left right marks)
      (writers : VisitorWriterPath profile ready base bindings reached peer checked canonical left right)
      (observed : PayloadPrefix.visible canonical = PayloadPrefix.visible checked)
      (frontier : ComponentStoreFrontier changes check canon (cancelAfterHookDecision subtask) (cancelAfterHookDecision subtask)
        left right trailing True)
      (terminal : trailing = [] ∨ (left.ctl = [] ∧ right.ctl = []))
      (residual : Steps profile ready (specDispatch ready base) left trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer (checked ++ trailing) finish
  | cancelParked {changes reached peer left right checked canonical trailing finish mark}
      (paths : OccurrenceTransport profile ready base bindings reached peer checked canonical left right [mark])
      (writers : VisitorWriterPath profile ready base bindings reached peer checked canonical left right)
      (observed : PayloadPrefix.visible canonical = PayloadPrefix.visible checked)
      (ending : CallbackSliceEnd profile ready base bindings changes left right trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer (checked ++ trailing) finish

def CallbackSlice (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (changes : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (checked canonical : Config (core3 grow) (HostState sig)) (actual : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ checkLabels canonLabels trailing reached peer,
    actual = checkLabels ++ trailing ∧
    ExecutedCallbackSegment profile ready base bindings changes checked canonical checkLabels canonLabels reached peer ∧
    CallbackSliceEnd profile ready base bindings changes reached peer trailing finish

/-- Start with the original active Core slot at a callout block and follow it
through the compared part of the mixed suffix, including actual resumes.
The ending retains the unconsumed checked residual. An absent occurrence
does not identify a later, equal saved frame as the original waiter. -/
def ParkedCoreCalloutSlice (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (changes : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (checked canonical : Config (core3 grow) (HostState sig)) (actual : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig)) : Prop :=
  open ReturnFrame.Occurrence in
  (actual = [] ∧ finish = checked) ∨
    ∃ checkLabels canonLabels trailing reached peer mark,
      actual = (.tau :: checkLabels) ++ trailing ∧
      OccurrenceTransport profile ready base bindings checked canonical (.tau :: checkLabels) (.tau :: canonLabels) reached peer ∧
      Trail profile ready (specDispatch ready base) checked (some (.active 0 0)) (.tau :: checkLabels) reached mark ∧
      Trail profile ready (specDispatch ready (LiveDispatch.host bindings base)) canonical (some (.active 0 0))
        (.tau :: canonLabels) peer mark ∧
      CallbackSliceEnd profile ready base bindings changes reached peer trailing finish

abbrev ParkedWaitCallbackSlice := ParkedCoreCalloutSlice (grow := grow) (sig := sig)

/-- The induction hypothesis available inside a reached give, including
callbacks with freshly extended substitutions. -/
def ShorterCallbackSlices (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig)) (budget : Nat) : Prop :=
  ∀ {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {checked canonical finish actual},
    actual.length < budget → Steps profile ready (specDispatch ready base) checked actual finish →
    HostFrame.Related.Paired changes checked canonical → CallbackSlice profile ready base bindings changes checked canonical actual finish

/-- A local give rule for the callback fold, called only at an extracted
install. To advance it must consume that install in a compared segment and
leave a checked residual from the supplied derivation. An unclassified
boundary is not a runtime refusal. -/
def CallbackGiveCrossing (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig)) : Prop :=
  ∀ {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {checked canonical next finish label trailing},
    GiveInstall bindings (specDispatch ready base) checked label next →
    Steps profile ready (specDispatch ready base) next trailing finish →
    HostFrame.Related.Paired changes checked canonical →
    ShorterCallbackSlices profile ready base bindings (label :: trailing).length →
    (∃ consumed canonLabels residual replied peer,
      trailing = consumed ++ residual ∧
      ExecutedCallbackSegment profile ready base bindings changes checked canonical (label :: consumed) canonLabels replied peer ∧
      Steps profile ready (specDispatch ready base) replied residual finish) ∨
    CallbackSlice profile ready base bindings changes checked canonical (label :: trailing) finish

/-- The silent install is available before comparing a callback, so the
recursive consumer can enter the actual checked tail at these coordinates. -/
structure PairedAllocatorInstall (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (first second : ReturnFrame.Continuation (core3 grow) (HostState sig))
    (checked canonical checkEntry canonEntry : Config (core3 grow) (HostState sig))
    (checkCount canonCount : Nat) : Prop where
  checkedRun : Steps profile ready (specDispatch ready base) checked (List.replicate checkCount .tau) checkEntry
  canonicalRun : Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) canonical
    (List.replicate canonCount .tau) canonEntry
  paired : HostFrame.Related.Paired (ReturnFrame.Extend older first second) checkEntry canonEntry

/-- A prefix can end before installation. Otherwise its original checked tail
provides the installed visitor's callback input and remaining boundary. -/
def InstalledCallbackSlice (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (first second : ReturnFrame.Continuation (core3 grow) (HostState sig))
    (checkEntry canonEntry : Config (core3 grow) (HostState sig)) (checkCount : Nat)
    (actual : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  actual.length < checkCount ∨ ∃ checkLabels canonLabels trailing reached peer,
    actual = List.replicate checkCount .tau ++ checkLabels ++ trailing ∧
    AllocatorCallbackPrefix profile ready base bindings older first second checkEntry canonEntry
      (some (checkLabels, canonLabels, peer)) (PayloadPrefix.visible checkLabels) reached ∧
    CallbackSliceEnd profile ready base bindings (ReturnFrame.Extend older first second) reached peer trailing finish

/-- Compare an actual residual string program under the fixed live give
dispatcher. Each local segment may trap; each entered allocator can expose
any finite classified prefix. Only a pop of its marked occurrence enters a
smaller program. The terminal consumer can compare the real descriptor. -/
def LiveStringReplay (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (cx : LiftLowerContext (core3 grow))
    (checkNext canonNext : Nat → Session grow sig (Ret (core3 grow)))
    (finish : Nat → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
      PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → Prop)
    (length : Nat) (left right : Config (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) : Prop :=
  open PayloadPrefix ReturnFrame.Occurrence in
  let checkDispatch := specDispatch ready base
  let canonDispatch := specDispatch ready (LiveDispatch.host bindings base)
  ∃ (store : CStore (core3 grow)) (result : Except TrapReason (StringFront length)) (labels : Trace grow sig),
    let lhs := localLeafEnd left left.host store check.thread check.frames check.rest
      (fun front : StringFront length => front.remaining cx >>= checkNext) result
    let rhs := localLeafEnd right right.host store canon.thread canon.frames canon.rest
      (fun front : StringFront length => front.remaining cx >>= canonNext) result
    LocalLeafLabels result labels ∧ CoreGrowthSteps profile ready checkDispatch left labels lhs ∧
    CoreGrowthSteps profile ready canonDispatch right labels rhs ∧
    PairedLeafSteps profile ready checkDispatch canonDispatch left right labels lhs rhs ∧
    OccurrenceTransport profile ready base bindings left right labels labels lhs rhs ∧
    ∀ front, result = .ok front →
      RetainsActiveSlots profile ready checkDispatch left labels lhs ∧
      RetainsActiveSlots profile ready canonDispatch right labels rhs ∧
      match front with
      | .done pointer => finish pointer lhs rhs check canon
      | .call pointer oldSize alignment size rest _ =>
        let first := stringPlanResume cx rest checkNext
        let second := stringPlanResume cx rest canonNext
        let firstEntry := LinkedCallback.stringReallocEntry ready bindings cx pointer oldSize alignment size rest checkNext lhs check
        let secondEntry := stringAllocatorEntry canonDispatch cx pointer oldSize alignment size rhs canon second
        PairedAllocatorInstall profile ready base bindings older first second lhs rhs firstEntry secondEntry 1 1 ∧
        ∀ {index seen reached}, AllocatorCallbackPrefix profile ready base bindings older first second firstEntry secondEntry index seen reached →
          ∃ checkLabels canonLabels reference mark,
            Steps profile ready checkDispatch lhs (.tau :: checkLabels) reached ∧
            Steps profile ready canonDispatch rhs (.tau :: canonLabels) reference ∧
            visible checkLabels = seen ∧ visible canonLabels = seen ∧
            HostFrame.Related.Paired (ReturnFrame.Extend older first second) reached reference ∧
            Core3.Grows lhs.store.core reached.store.core ∧
            AllocatorMark profile ready base bindings older firstEntry secondEntry checkLabels canonLabels reached reference mark ∧
            OccurrenceTransport profile ready base bindings lhs rhs (.tau :: checkLabels) (.tau :: canonLabels) reached reference [mark] ∧
            index.Matches checkLabels canonLabels reference ∧
            ∀ (value : Nat) (cursor : Cursor (E := core3 grow) (HostState sig)), mark = some (.active 0 0) →
              reached.ctl = { cursor with frames := .prog first :: cursor.frames }.control (.pure (.nat value)) →
              ∃ peer : Cursor (E := core3 grow) (HostState sig),
                let after := { reached with ctl := cursor.control (first (.nat value)) }
                let referenceAfter := { reference with ctl := peer.control (second (.nat value)) }
                RetainsActiveSlots profile ready checkDispatch lhs (.tau :: checkLabels ++ [.tau]) after ∧
                RetainsActiveSlots profile ready canonDispatch rhs (.tau :: canonLabels ++ [.tau]) referenceAfter ∧
                OccurrenceTransport profile ready base bindings lhs rhs (.tau :: checkLabels ++ [.tau])
                  (.tau :: canonLabels ++ [.tau]) after referenceAfter ∧
                LiveStringReplay profile ready base bindings older cx checkNext canonNext finish rest.length after referenceAfter cursor peer
termination_by length

/-- A string-plan traversal stops at the actual descriptor continuation, a
trap, a finite cut before the next local frontier, or an installed callback
whose exact mark has not popped with a pointer. -/
inductive StringSliceEnd (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (describe : Nat → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
      PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → Prop)
    (checked canonical : Config (core3 grow) (HostState sig))
    (trailing : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) :
    List (Option ReturnFrame.Occurrence.Location) → Prop where
  | descriptor {pointer cursor peer} (reached : describe pointer checked canonical cursor peer) :
      StringSliceEnd profile ready base bindings older describe checked canonical trailing finish []
  | trap (left : checked.ctl = []) (right : canonical.ctl = []) :
      StringSliceEnd profile ready base bindings older describe checked canonical trailing finish []
  | localPrefix {reached remaining} (nonempty : remaining ≠ [])
      (localTail : Steps profile ready (specDispatch ready base) finish remaining reached) :
      StringSliceEnd profile ready base bindings older describe checked canonical trailing finish []
  | localChoice {leading taken suffix middle next} (split : trailing = leading ++ taken :: suffix)
      (choice : workerBranchLabel taken)
      (shared : Steps profile ready (specDispatch ready base) checked leading middle)
      (step : Step profile ready (specDispatch ready base) middle taken next)
      (tail : Steps profile ready (specDispatch ready base) next suffix finish) :
      StringSliceEnd profile ready base bindings older describe checked canonical trailing finish []
  | installPrefix (exhausted : trailing = []) :
      StringSliceEnd profile ready base bindings older describe checked canonical trailing finish []
  | collectionInstall (exhausted : trailing = []) :
      StringSliceEnd profile ready base bindings older describe checked canonical trailing finish []
  | collectionRange {reached remaining marks} (nonempty : remaining ≠ [])
      (localTail : Steps profile ready (specDispatch ready base) finish remaining reached) :
      StringSliceEnd profile ready base bindings older describe checked canonical trailing finish marks
  | callback {checkEntry canonEntry checkLabels canonLabels mark first second}
      (tracked : AllocatorMark profile ready base bindings older checkEntry canonEntry checkLabels canonLabels checked canonical mark)
      (paired : HostFrame.Related.Paired (ReturnFrame.Extend older first second) checked canonical)
      (ending : CallbackSliceEnd profile ready base bindings (ReturnFrame.Extend older first second) checked canonical trailing finish)
      (notPopped : trailing = [] ∨ mark ≠ some (.active 0 0) ∨ ¬ ∃ (pointer : Nat)
        (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)),
        checked.ctl = { cursor with frames := .prog first :: cursor.frames }.control (.pure (.nat pointer))) :
      StringSliceEnd profile ready base bindings older describe checked canonical trailing finish [mark]

/-- The compared part of an actual checked string run. The residual is
always an execution from the reached checked state, not a new callback or
a canonical execution of the remainder. -/
def StringRunSlice (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (describe : Nat → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
      PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → Prop)
    (checked canonical : Config (core3 grow) (HostState sig)) (actual : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ checkLabels canonLabels trailing reached peer marks,
    actual = checkLabels ++ trailing ∧
    PayloadPrefix.visible canonLabels = PayloadPrefix.visible checkLabels ∧
    OccurrenceTransport profile ready base bindings checked canonical checkLabels canonLabels reached peer marks ∧
    reached.store = peer.store ∧ Steps profile ready (specDispatch ready base) reached trailing finish ∧
    StringSliceEnd profile ready base bindings older describe reached peer trailing finish marks

/-- The same reached string-shaped cut, with writer evidence indexed by
the very paths used for occurrence transport. -/
def StringRunSliceWithWriters (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (describe : Nat → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
      PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → Prop)
    (start incoming : Config (core3 grow) (HostState sig)) (actual : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ checked canonical trailing left right marks, actual = checked ++ trailing ∧
    PayloadPrefix.visible canonical = PayloadPrefix.visible checked ∧
    OccurrenceTransport profile ready base bindings start incoming checked canonical left right marks ∧ left.store = right.store ∧
    Steps profile ready (specDispatch ready base) left trailing finish ∧
    VisitorWriterPath profile ready base bindings start incoming checked canonical left right ∧
    StringSliceEnd profile ready base bindings older describe left right trailing finish marks

/-- Two finite paths, compared at their reached stores and visible labels. -/
def ComparedPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (leftStart rightStart : Config (core3 grow) (HostState sig)) (seen : Trace grow sig)
    (left right : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ checkLabels canonLabels,
    Steps profile ready (specDispatch ready base) leftStart checkLabels left ∧
    Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) rightStart canonLabels right ∧
    PayloadPrefix.visible checkLabels = seen ∧ PayloadPrefix.visible canonLabels = seen ∧ left.store = right.store

/-- A compared prefix with a shared trajectory for every source coordinate.
The reached coordinate may differ from the source, or be absent on both sides. -/
def ComparedOccurrencePaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (leftStart rightStart : Config (core3 grow) (HostState sig)) (seen : Trace grow sig)
    (left right : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ checkLabels canonLabels,
    CoupledOccurrencePaths profile ready base bindings leftStart rightStart checkLabels canonLabels left right ∧
    PayloadPrefix.visible checkLabels = seen ∧ PayloadPrefix.visible canonLabels = seen ∧ left.store = right.store

/-- One pair of reached traces witnesses both the visible prefix and the
transport of all enclosing marks. No temporary allocator mark remains open
at this cut. -/
def ComparedOccurrenceTransport (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (leftStart rightStart : Config (core3 grow) (HostState sig)) (seen : Trace grow sig)
    (left right : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ checkLabels canonLabels,
    OccurrenceTransport profile ready base bindings leftStart rightStart checkLabels canonLabels left right ∧
    PayloadPrefix.visible checkLabels = seen ∧ PayloadPrefix.visible canonLabels = seen ∧ left.store = right.store

/-- Cumulative all-location trails through the actual string plan. A finite
callback path need not reach a pop. Only the installed frame's actual return
continues the decreasing residual plan. -/
def LiveStringOccurrences (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (cx : LiftLowerContext (core3 grow))
    (checkNext canonNext : Nat → Session grow sig (Ret (core3 grow)))
    (leftStart rightStart : Config (core3 grow) (HostState sig))
    (finish : Nat → Trace grow sig → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
      PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → Prop)
    (length : Nat) (left right : Config (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) (seen : Trace grow sig)
    (leftBody : Config (core3 grow) (HostState sig) := left) (rightBody : Config (core3 grow) (HostState sig) := right) : Prop :=
  open PayloadPrefix ReturnFrame.Occurrence in
  ∃ (store : CStore (core3 grow)) (result : Except TrapReason (StringFront length)) (labels : Trace grow sig),
    let lhs := localLeafEnd left left.host store check.thread check.frames check.rest
      (fun front : StringFront length => front.remaining cx >>= checkNext) result
    let rhs := localLeafEnd right right.host store canon.thread canon.frames canon.rest
      (fun front : StringFront length => front.remaining cx >>= canonNext) result
    LocalLeafLabels result labels ∧
    ComparedOccurrencePaths profile ready base bindings leftStart rightStart (seen ++ visible labels) lhs rhs ∧
    (∃ checked canonical, OccurrenceTransport profile ready base bindings leftBody rightBody checked canonical lhs rhs) ∧
    match result with
    | .error _ => lhs.ctl = [] ∧ rhs.ctl = []
    | .ok (.done pointer) => finish pointer (seen ++ visible labels) lhs rhs check canon
    | .ok (.call pointer oldSize alignment size rest _) =>
      let first := stringPlanResume cx rest checkNext
      let second := stringPlanResume cx rest canonNext
      let firstEntry := LinkedCallback.stringReallocEntry ready bindings cx pointer oldSize alignment size rest checkNext lhs check
      let secondEntry := stringAllocatorEntry (specDispatch ready (LiveDispatch.host bindings base))
        cx pointer oldSize alignment size rhs canon second
      PairedAllocatorInstall profile ready base bindings older first second lhs rhs firstEntry secondEntry 1 1 ∧
      ∀ {index observed reached}, AllocatorCallbackPrefix profile ready base bindings older first second firstEntry secondEntry index observed reached →
        ∃ checkLabels canonLabels reference mark,
          AllocatorMark profile ready base bindings older firstEntry secondEntry checkLabels canonLabels reached reference mark ∧
          HostFrame.Related.Paired (ReturnFrame.Extend older first second) reached reference ∧
          ComparedOccurrencePaths profile ready base bindings leftStart rightStart (seen ++ observed) reached reference ∧
          (∃ checked canonical, OccurrenceTransport profile ready base bindings leftBody rightBody checked canonical reached reference [mark]) ∧
          index.Matches checkLabels canonLabels reference ∧
          ∀ (value : Nat) (cursor : Cursor (E := core3 grow) (HostState sig)), mark = some (.active 0 0) →
            reached.ctl = { cursor with frames := .prog first :: cursor.frames }.control (.pure (.nat value)) →
            ∃ peer : Cursor (E := core3 grow) (HostState sig),
              let after := { reached with ctl := cursor.control (first (.nat value)) }
              let referenceAfter := { reference with ctl := peer.control (second (.nat value)) }
              ComparedOccurrencePaths profile ready base bindings leftStart rightStart (seen ++ observed) after referenceAfter ∧
              LiveStringOccurrences profile ready base bindings older cx checkNext canonNext leftStart rightStart finish
                rest.length after referenceAfter cursor peer (seen ++ observed) leftBody rightBody
termination_by length

/-- A compared prefix with occurrence trails for active slots. The starting
offset accounts for older slots below an allocator frame that is popped. -/
def ComparedSlots (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (leftStart rightStart : Config (core3 grow) (HostState sig)) (seen : Trace grow sig)
    (left right : Config (core3 grow) (HostState sig)) (offset : Nat := 0) : Prop :=
  open ReturnFrame.Occurrence in
  ∃ checkLabels canonLabels,
    (∀ depth, Prefix profile ready (specDispatch ready base) leftStart (.active 0 (depth + offset)) checkLabels left (.active 0 depth)) ∧
    (∀ depth, Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base))
      rightStart (.active 0 (depth + offset)) canonLabels right (.active 0 depth)) ∧
    PayloadPrefix.visible checkLabels = seen ∧ PayloadPrefix.visible canonLabels = seen

/-- A finite allocation endpoint preserves the trajectory of every enclosing
active occurrence from traversal entry, not just the latest installed frame.
After installation an enclosing occurrence can move to a saved slot or be
lost; neither outcome is an allocator return. -/
def ComparedAllocatorPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (leftStart rightStart : Config (core3 grow) (HostState sig)) (seen : Trace grow sig)
    (left right : Config (core3 grow) (HostState sig)) (offset : Nat := 0) : Prop :=
  open ReturnFrame.Occurrence in
  ∃ checkLabels canonLabels,
    (∀ depth, ∃ reached,
      Trail profile ready (specDispatch ready base) leftStart (some (.active 0 (depth + offset))) checkLabels left reached ∧
      Trail profile ready (specDispatch ready (LiveDispatch.host bindings base))
        rightStart (some (.active 0 (depth + offset))) canonLabels right reached) ∧
    PayloadPrefix.visible checkLabels = seen ∧ PayloadPrefix.visible canonLabels = seen ∧ left.store = right.store

/-- A continuation receives the visible history at its actual reached pair. -/
abbrev TrailFinish (grow : SingleThreaded.GrowOracle) (sig : Signature) :=
  Trace grow sig → LinkedCallback.MemorySequence.Finish grow sig

abbrev TrailFieldComparison (grow : SingleThreaded.GrowOracle) (sig : Signature) :=
  Stored.Endpoints.RecordLower.Field → Nat → Nat → LinkedCallback.MemorySequence.CheckNext grow sig →
    LinkedCallback.MemorySequence.CanonNext grow sig → TrailFinish grow sig → TrailFinish grow sig

abbrev IssueProgram (grow : SingleThreaded.GrowOracle) (sig : Signature) :=
  Stored.Endpoints.RecordLower.Issue → Session grow sig (Ret (core3 grow))

/-- All recursive wrappers either skip the suffix or add an issue index.
The sink receives the actual reached continuation, not a replay plan. -/
structure RefusalSink (grow : SingleThreaded.GrowOracle) (sig : Signature) where
  admits : IssueProgram grow sig → Prop
  nested : ∀ next, admits next → ∀ index, admits (fun issue => next (.nested index issue))
  exit : IssueProgram grow sig → Stored.Endpoints.RecordLower.Issue → Trace grow sig →
    Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
    PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → Prop

def RefusalSink.ignore : RefusalSink grow sig := ⟨fun _ => True, fun _ _ _ => trivial, fun _ _ _ _ _ _ => True⟩

def RefusalSink.Covers (sink : RefusalSink grow sig) (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (start incoming : Config (core3 grow) (HostState sig)) (offset : Nat) : Prop :=
  ∀ next, sink.admits next → ∀ issue seen left right check,
    left.ctl = check.control (next issue) → left.store = right.store →
    ComparedSlots profile ready base bindings start incoming seen left right offset → sink.exit next issue seen left right check

abbrev FlatTrailFinish (grow : SingleThreaded.GrowOracle) (sig : Signature) :=
  List FlatValue → Trace grow sig → LinkedCallback.MemorySequence.Finish grow sig

abbrev FlatFieldTrail (grow : SingleThreaded.GrowOracle) (sig : Signature) :=
  Stored.Endpoints.RecordLower.Field → Nat → LinkedCallback.FlatSequenceCheckNext grow sig →
    LinkedCallback.FlatSequenceCanonNext grow sig → FlatTrailFinish grow sig → TrailFinish grow sig

/-- Local flat induction rule at a reached field. Only common success can
advance the sequence. Refusals use the checked error continuation; other
exits are represented by the field's own path relation. -/
def DerivesFlatFieldTrailWith (history : Trace grow sig → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) → Prop)
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (origin : CStore (core3 grow))
    (destination : RecordDestination) (inst : InstId) (sink : RefusalSink grow sig)
    (path : FlatFieldTrail grow sig) (item : Stored.Endpoints.RecordLower.Field) : Prop :=
  open Stored.Endpoints.RecordLower in
  ∀ index checkNext canonNext finish before left right check canon,
    LinkedCallback.ChildFrameOver older left right check canon → Core3.Grows origin.core left.store.core →
    history before left right →
    sink.admits (fun issue => checkNext (.error issue)) →
    left.ctl = check.control (OwnedMemory.Claims.Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width item index .flat >>= checkNext) →
    right.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width item .flat >>= canonNext) →
    (∀ words seen lhs rhs cursor peer, LinkedCallback.ChildFrameOver older lhs rhs cursor peer →
      Core3.Grows origin.core lhs.store.core → history seen lhs rhs →
      lhs.ctl = cursor.control (checkNext (.ok words)) → rhs.ctl = peer.control (canonNext words) →
      finish words seen lhs rhs cursor peer) →
    path item index checkNext canonNext finish before left right check canon


abbrev DerivesFlatFieldTrail (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (origin : CStore (core3 grow))
    (start incoming : Config (core3 grow) (HostState sig)) (offset : Nat)
    (destination : RecordDestination) (inst : InstId) (sink : RefusalSink grow sig)
    (path : FlatFieldTrail grow sig) (item : Stored.Endpoints.RecordLower.Field) : Prop :=
  DerivesFlatFieldTrailWith (fun seen left right => ComparedSlots profile ready base bindings start incoming seen left right offset)
    older origin destination inst sink path item

/-- Thread the actual flat words and cumulative occurrence history in order.
An error continuation does not run the remaining fields on either side. -/
def flatSequencePaths (destination : RecordDestination) (inst : InstId) (child : FlatFieldTrail grow sig)
    (checkNext : LinkedCallback.FlatSequenceCheckNext grow sig) (canonNext : LinkedCallback.FlatSequenceCanonNext grow sig)
    (finish : FlatTrailFinish grow sig) : List Stored.Endpoints.RecordLower.Field → Nat → List FlatValue → TrailFinish grow sig
  | [], _, leading => finish leading
  | item :: rest, index, leading =>
    open LinkedCallback in
    child item index
      (fun verdict => match verdict with
        | .error issue => checkNext (.error issue)
        | .ok words => flatSequenceChecked destination inst rest (index + 1) (leading ++ words) checkNext)
      (fun words => flatSequenceCanonical destination inst rest (leading ++ words) canonNext)
      (fun words => flatSequencePaths destination inst child checkNext canonNext finish rest (index + 1) (leading ++ words))

/-- A compiled field advances its sibling only at the actual success
continuation, carrying the chosen occurrence history to that reached pair. -/
def LiftsFieldPathsWith (history : Trace grow sig → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) → Prop)
    (field : LinkedCallback.MemorySequence.FieldComparison grow sig) (paths : TrailFieldComparison grow sig)
    (sink : RefusalSink grow sig := .ignore) : Prop :=
  ∀ item index address left right check canon checkNext canonNext finish visit before,
    field item index address left right check canon checkNext canonNext finish →
    history before left right →
    left.store = right.store →
    sink.admits (fun issue => checkNext (.error issue)) →
    (∀ seen lhs rhs cursor peer,
      history seen lhs rhs → lhs.store = rhs.store →
      finish lhs rhs cursor peer → visit seen lhs rhs cursor peer) →
    paths item index address checkNext canonNext visit before left right check canon

abbrev LiftsFieldPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (start incoming : Config (core3 grow) (HostState sig)) (offset : Nat)
    (field : LinkedCallback.MemorySequence.FieldComparison grow sig) (paths : TrailFieldComparison grow sig)
    (sink : RefusalSink grow sig := .ignore) : Prop :=
  LiftsFieldPathsWith (fun seen left right => ComparedSlots profile ready base bindings start incoming seen left right offset)
    field paths sink

abbrev LiftsFieldOccurrencePaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (start incoming : Config (core3 grow) (HostState sig))
    (field : LinkedCallback.MemorySequence.FieldComparison grow sig) (paths : TrailFieldComparison grow sig)
    (sink : RefusalSink grow sig := .ignore) : Prop :=
  LiftsFieldPathsWith (ComparedOccurrencePaths profile ready base bindings start incoming) field paths sink

abbrev LiftsFieldTransportPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (start incoming : Config (core3 grow) (HostState sig))
    (field : LinkedCallback.MemorySequence.FieldComparison grow sig) (paths : TrailFieldComparison grow sig)
    (sink : RefusalSink grow sig := .ignore) : Prop :=
  LiftsFieldPathsWith (ComparedOccurrenceTransport profile ready base bindings start incoming) field paths sink

/-- Follow the same slots, width reads and suffix programs as `ReplayBetween`,
but hand the cumulative visible history to the remaining sibling traversal. -/
def replayBetweenPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (mode : LinkedCallback.MemorySequence.Track) (destination : RecordDestination) (inst : InstId)
    (child : TrailFieldComparison grow sig) (checkNext : LinkedCallback.MemorySequence.CheckNext grow sig)
    (canonNext : LinkedCallback.MemorySequence.CanonNext grow sig) (finish : TrailFinish grow sig) :
    List Stored.Endpoints.RecordLower.Field → Nat → Nat → TrailFinish grow sig
  | [], _, _, before, left, right, check, canon => finish before left right check canon
  | item :: rest, index, cursor, before, left, right, check, canon =>
    open LinkedCallback.MemorySequence in
    let slot := mode.slot destination.width item cursor
    let nextCheck := checkTail mode destination inst rest (index + 1) slot.2 checkNext
    let nextCanon := canonTail mode destination inst rest slot.2 canonNext
    let reference := focus mode destination inst item cursor right canon nextCanon
    ComparedOccurrencePaths profile ready base bindings left right [] left reference ∧
    child item index slot.1 nextCheck nextCanon
      (replayBetweenPaths profile ready base bindings mode destination inst child checkNext canonNext finish
        rest (index + 1) slot.2) before left reference check canon

/-- A cumulative view of the actual string plan. Compare a finite stopped
allocator prefix at its reached state; to continue, it must pop the marked
occurrence. Only a finished plan reaches the consumer. -/
def LiveStringPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (cx : LiftLowerContext (core3 grow))
    (checkNext canonNext : Nat → Session grow sig (Ret (core3 grow)))
    (leftStart rightStart : Config (core3 grow) (HostState sig))
    (finish : Nat → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
      PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → PayloadPrefix.Cursor (E := core3 grow) (HostState sig) →
      Trace grow sig → Prop)
    (length : Nat) (left right : Config (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) (seen : Trace grow sig) (offset : Nat := 0) : Prop :=
  open PayloadPrefix ReturnFrame.Occurrence in
  let checkDispatch := specDispatch ready base
  let canonDispatch := specDispatch ready (LiveDispatch.host bindings base)
  ∃ (store : CStore (core3 grow)) (result : Except TrapReason (StringFront length)) (labels : Trace grow sig),
    let lhs := localLeafEnd left left.host store check.thread check.frames check.rest
      (fun front : StringFront length => front.remaining cx >>= checkNext) result
    let rhs := localLeafEnd right right.host store canon.thread canon.frames canon.rest
      (fun front : StringFront length => front.remaining cx >>= canonNext) result
    LocalLeafLabels result labels ∧ Steps profile ready checkDispatch left labels lhs ∧ Steps profile ready canonDispatch right labels rhs ∧
    match result with
    | .error reason => lhs.ctl = [] ∧ rhs.ctl = [] ∧
      ComparedPaths profile ready base bindings leftStart rightStart (seen ++ [.trap reason]) lhs rhs
    | .ok (.done pointer) => ComparedSlots profile ready base bindings leftStart rightStart seen lhs rhs offset ∧
      finish pointer lhs rhs check canon seen
    | .ok (.call pointer oldSize alignment size rest _) =>
      let first := stringPlanResume cx rest checkNext
      let second := stringPlanResume cx rest canonNext
      let firstEntry := LinkedCallback.stringReallocEntry ready bindings cx pointer oldSize alignment size rest checkNext lhs check
      let secondEntry := stringAllocatorEntry canonDispatch cx pointer oldSize alignment size rhs canon second
      PairedAllocatorInstall profile ready base bindings older first second lhs rhs firstEntry secondEntry 1 1 ∧
      ∀ {index observed reached}, AllocatorCallbackPrefix profile ready base bindings older first second firstEntry secondEntry index observed reached →
        ∃ checkLabels canonLabels reference mark,
          AllocatorMark profile ready base bindings older firstEntry secondEntry checkLabels canonLabels reached reference mark ∧
          HostFrame.Related.Paired (ReturnFrame.Extend older first second) reached reference ∧
          ComparedAllocatorPaths profile ready base bindings leftStart rightStart (seen ++ observed) reached reference offset ∧
          index.Matches checkLabels canonLabels reference ∧
          ∀ (value : Nat) (cursor : Cursor (E := core3 grow) (HostState sig)), mark = some (.active 0 0) →
            reached.ctl = { cursor with frames := .prog first :: cursor.frames }.control (.pure (.nat value)) →
            ∃ peer : Cursor (E := core3 grow) (HostState sig),
              let after := { reached with ctl := cursor.control (first (.nat value)) }
              let referenceAfter := { reference with ctl := peer.control (second (.nat value)) }
              LiveStringPaths profile ready base bindings older cx checkNext canonNext leftStart rightStart finish
                rest.length after referenceAfter cursor peer (seen ++ observed) offset
termination_by length

/-- Validate the pointer from an actual marked return. The invalid branches
trap at the reached stores. The valid branch exposes the real checked live
verdict and the canonical child-entry program, before either executes children. -/
def CollectionRangeCut (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (checked canonical : Config (core3 grow) (HostState sig))
    (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (destination : RecordDestination) (area : ABI.Layout) (count pointer : Nat)
    (plan : List Stored.Endpoints.RecordLower.Object)
    (checkNext : Nat → Except Stored.Endpoints.RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Nat → Session grow sig (Ret (core3 grow))) : Prop :=
  let checkedDispatch := specDispatch ready base
  let canonDispatch := specDispatch ready (LiveDispatch.host bindings base)
  let traps := fun reason =>
    (∃ steps, Steps profile ready checkedDispatch checked (List.replicate steps .tau ++ [.trap reason]) (StepDefs.trapCfg checked)) ∧
    (∃ steps, Steps profile ready canonDispatch canonical (List.replicate steps .tau ++ [.trap reason]) (StepDefs.trapCfg canonical))
  ∃ canonCursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig), ∃ bytes,
    (core3 grow).memAddrType? checked.store.core destination.memory = some destination.width ∧
    (core3 grow).memSize? checked.store.core destination.memory = some bytes ∧
    LinkedCallback.ChildFrameOver older checked canonical cursor canonCursor ∧
    if pointer ≠ ABI.alignTo pointer area.alignment then traps .unalignedPointer
    else if pointer + count * area.size ≤ bytes then
      (∃ trace, (∀ label ∈ trace, label = .tau) ∧ ReturnFrame.Occurrence.RetainsBelowTop profile ready checkedDispatch checked trace
        { checked with ctl := cursor.control (checkNext pointer (OwnedMemory.Claims.Record.prepare checked.store checked.host.writer plan)) }) ∧
      (∃ trace, (∀ label ∈ trace, label = .tau) ∧ ReturnFrame.Occurrence.RetainsBelowTop profile ready canonDispatch canonical trace
        { canonical with ctl := canonCursor.control (canonNext pointer) })
    else traps .outOfBounds

/-- Extend the exact enclosing trail across a collection's reached range
suffix. The input mark is the allocator's returned top occurrence, not an
arbitrary frame with an equal continuation. -/
def CollectionRangeTransport (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (checked canonical lhs rhs : Config (core3 grow) (HostState sig)) (observed : Trace grow sig)
    (traceShape : Trace grow sig → Trace grow sig → Prop := fun _ _ => True) : Prop :=
  ∀ {leftStart rightStart checkTrace canonTrace},
    OccurrenceTransport profile ready base bindings leftStart rightStart checkTrace canonTrace checked canonical [some (.active 0 0)] →
    ∃ leftTail rightTail, OccurrenceTransport profile ready base bindings leftStart rightStart
      (checkTrace ++ leftTail) (canonTrace ++ rightTail) lhs rhs ∧
      PayloadPrefix.visible leftTail = observed ∧ PayloadPrefix.visible rightTail = observed ∧ lhs.store = rhs.store ∧
      PayloadPrefix.PairedLocalPath profile ready (specDispatch ready base) (specDispatch ready (LiveDispatch.host bindings base))
        checked canonical leftTail rightTail lhs rhs ∧ traceShape leftTail rightTail

open Stored.OwnedMemory.Claims.Record in
/-- In the in-bounds route the marked pop and range/store reads reach a
checked-only `hostGet`. Raw is already at the pending child entry. -/
structure CollectionPrepareSite (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (checked canonical left right reader : Config (core3 grow) (HostState sig))
    (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (plan : List Stored.Endpoints.RecordLower.Object)
    (next : Except Stored.Endpoints.RecordLower.Issue Unit → Session grow sig (Ret (core3 grow))) : Prop where
  checkedTracks : RangeReturnTrails profile ready (specDispatch ready base) checked [.tau, .tau, .tau] reader
  rawTracks : RangeReturnTrails profile ready (specDispatch ready (LiveDispatch.host bindings base)) canonical [.tau, .tau] right
  focus : reader.ctl = cursor.control (.op .hostGet (fun state => next (prepare reader.store state.writer plan)))
  read : PayloadPrefix.SilentLocalStep profile ready (specDispatch ready base) reader left
  checkedHost : reader.host = checked.host
  rawHost : right.host = canonical.host
  sameStore : reader.store = right.store

/-- Cumulative paths through the real collection return. A fresh verdict
selects the checked continuation only; the canonical child program is still
pending. Range traps instead end both paths at the reached lockdown states. -/
def CollectionRangeOccurrences (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (leftStart rightStart checked canonical : Config (core3 grow) (HostState sig)) (seen : Trace grow sig)
    (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (destination : RecordDestination) (area : ABI.Layout) (count pointer : Nat)
    (plan : List Stored.Endpoints.RecordLower.Object)
    (checkNext : Nat → Except Stored.Endpoints.RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Nat → Session grow sig (Ret (core3 grow))) : Prop :=
  let traps := fun reason => ComparedOccurrencePaths profile ready base bindings leftStart rightStart
    (seen ++ [.trap reason]) (StepDefs.trapCfg checked) (StepDefs.trapCfg canonical) ∧
    CollectionRangeTransport profile ready base bindings checked canonical (StepDefs.trapCfg checked) (StepDefs.trapCfg canonical) [.trap reason]
  ∃ bytes, (core3 grow).memAddrType? checked.store.core destination.memory = some destination.width ∧
    (core3 grow).memSize? checked.store.core destination.memory = some bytes ∧
    if pointer ≠ ABI.alignTo pointer area.alignment then traps .unalignedPointer
    else if pointer + count * area.size ≤ bytes then
      ∃ canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig),
        let verdict := OwnedMemory.Claims.Record.prepare checked.store checked.host.writer plan
        let left := { checked with ctl := cursor.control (checkNext pointer verdict) }
        let right := { canonical with ctl := canon.control (canonNext pointer) }
        LinkedCallback.ChildFrameOver older left right cursor canon ∧
        (∃ labels, (∀ label ∈ labels, label = .tau) ∧
          RangeReturnTrails profile ready (specDispatch ready base) checked labels left) ∧
        (∃ labels, (∀ label ∈ labels, label = .tau) ∧
          RangeReturnTrails profile ready (specDispatch ready (LiveDispatch.host bindings base)) canonical labels right) ∧
        ComparedOccurrencePaths profile ready base bindings leftStart rightStart seen left right ∧
        CollectionRangeTransport profile ready base bindings checked canonical left right []
          (fun lhs rhs => lhs = [.tau, .tau, .tau, .tau] ∧ rhs = [.tau, .tau]) ∧
        ∃ reader, CollectionPrepareSite profile ready base bindings checked canonical left right reader cursor plan (checkNext pointer)
    else traps .outOfBounds

/-- Entry into the exact recursive bodies of a nested collection after its
marked allocator returns, range checks pass and a fresh reservation succeeds.
The all-location trail starts at this field's entry, while the active-slot
trail can start earlier. Both end at the same reached visitor states.
Memory-map placement keeps its allocation-time mode. -/
def LiveCollectionChildren (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (destination : RecordDestination) (inst : InstId) (type element : Stored.TypeOf)
    (entries : List Stored.Endpoints.RecordLower.Field) (index : Nat) (output : Stored.Lower.Output)
    (checkNext : Except Stored.Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (start incoming checked canonical : Config (core3 grow) (HostState sig)) (pointer bytes : Nat)
    (check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) (observed localSeen : Trace grow sig)
    (visit : LinkedCallback.MemorySequence.Finish grow sig := fun _ _ _ _ => True)
    (leftStart : Config (core3 grow) (HostState sig) := start)
    (rightStart : Config (core3 grow) (HostState sig) := incoming) (offset : Nat := 0) : Prop :=
  open Stored.Endpoints.RecordLower ABI PayloadPrefix in
  let area := layout destination.width element
  let mode := CanonicalTree.EntryMode.forOutput destination.width type output
  ∃ left right canon,
    ComparedSlots profile ready base bindings leftStart rightStart observed left right offset ∧
    ComparedOccurrencePaths profile ready base bindings start incoming localSeen left right ∧
    ComparedOccurrenceTransport profile ready base bindings start incoming localSeen left right ∧
    LinkedCallback.ChildFrameOver older left right check canon ∧
    (core3 grow).memAddrType? left.store.core destination.memory = some destination.width ∧
    (core3 grow).memSize? left.store.core destination.memory = some bytes ∧
    pointer = alignTo pointer area.alignment ∧ pointer + entries.length * area.size ≤ bytes ∧
    Core3.Grows start.store.core left.store.core ∧
    left.ctl = check.control (checkedCollectionTail destination inst entries area index output pointer (.ok ()) >>= checkNext) ∧
    right.ctl = canon.control (canonicalCollectionTail destination inst entries area output pointer mode >>= canonNext) ∧
    CollectionRangeTransport profile ready base bindings checked canonical left right [] ∧
    visit left right check canon

/-- The unsuccessful branches of a marked range return, measured from the
recursive body origin and from the local field entry. Range traps run on both
sides. A fresh reservation failure follows only the checked issue continuation;
the canonical cursor is at its unexecuted child program. -/
def CollectionRangePaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (leftStart rightStart : Config (core3 grow) (HostState sig)) (observed : Trace grow sig) (offset : Nat)
    (destination : RecordDestination) (area : ABI.Layout) (entries : List Stored.Endpoints.RecordLower.Field)
    (pointer : Nat) (checked canonical : Config (core3 grow) (HostState sig))
    (check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (refuse : IssueProgram grow sig) (wrap : Stored.Endpoints.RecordLower.Issue → Stored.Endpoints.RecordLower.Issue)
    (children : Session grow sig (Ret (core3 grow)))
    (leftEntry rightEntry : Config (core3 grow) (HostState sig)) (localSeen : Trace grow sig)
    (sink : RefusalSink grow sig := .ignore) : Prop :=
  open Stored.Endpoints.RecordLower in
  let trap := fun reason => ComparedPaths profile ready base bindings leftStart rightStart (observed ++ [.trap reason])
    (StepDefs.trapCfg checked) (StepDefs.trapCfg canonical) ∧
    ComparedOccurrencePaths profile ready base bindings leftEntry rightEntry (localSeen ++ [.trap reason])
      (StepDefs.trapCfg checked) (StepDefs.trapCfg canonical) ∧
    ComparedOccurrenceTransport profile ready base bindings leftEntry rightEntry (localSeen ++ [.trap reason])
      (StepDefs.trapCfg checked) (StepDefs.trapCfg canonical)
  ∃ bytes, (core3 grow).memSize? checked.store.core destination.memory = some bytes ∧
    if pointer ≠ ABI.alignTo pointer area.alignment then trap .unalignedPointer
    else if pointer + entries.length * area.size ≤ bytes then
      ∀ issue, OwnedMemory.Claims.Record.prepare checked.store checked.host.writer (Field.listObjects entries) = .error issue →
        ∃ canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig),
          let stopped := { checked with ctl := check.control (refuse (wrap issue)) }
          let reference := { canonical with ctl := canon.control children }
          checked.store = canonical.store ∧ ComparedSlots profile ready base bindings leftStart rightStart observed
            stopped reference offset ∧
          ComparedOccurrencePaths profile ready base bindings leftEntry rightEntry localSeen stopped reference ∧
          ComparedOccurrenceTransport profile ready base bindings leftEntry rightEntry localSeen stopped reference ∧
          sink.exit refuse (wrap issue) observed stopped reference check
    else trap .outOfBounds

/-- Finite callback paths for an actual dynamic child. A live mark at the
natural-pointer return is required to inspect the range. Failed range checks
trap, and a failed fresh reservation does not enter the children. The
all-location trails start before this field's preflight and install. -/
def LiveCollectionPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (destination : RecordDestination) (inst : InstId) (type element : Stored.TypeOf)
    (entries : List Stored.Endpoints.RecordLower.Field) (index : Nat) (output : Stored.Lower.Output)
    (checkNext : Except Stored.Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (start incoming : Config (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (visit : Nat → Nat → TrailFinish grow sig := fun _ _ _ _ _ _ _ => True)
    (leftStart : Config (core3 grow) (HostState sig) := start)
    (rightStart : Config (core3 grow) (HostState sig) := incoming) (leading : Trace grow sig := []) (offset : Nat := 0)
    (sink : RefusalSink grow sig := .ignore) : Prop :=
  open Stored.Endpoints.RecordLower ABI PayloadPrefix in
  let area := layout destination.width element
  let mode := CanonicalTree.EntryMode.forOutput destination.width type output
  let first := checkedCollectionResume destination inst entries area index output checkNext
  let second := canonicalCollectionResume destination inst entries area output canonNext mode
  let leftEntry := collectionEntry destination inst area entries.length (specDispatch ready base) start check first
  let rightEntry := collectionEntry destination inst area entries.length (specDispatch ready (LiveDispatch.host bindings base))
    incoming canon second
  PairedAllocatorInstall profile ready base bindings older first second start incoming leftEntry rightEntry 3 2 ∧
  ∀ {pathIndex seen finish}, AllocatorCallbackPrefix profile ready base bindings older first second leftEntry rightEntry pathIndex seen finish →
    ∃ checkLabels canonLabels reached mark,
      AllocatorMark profile ready base bindings older leftEntry rightEntry checkLabels canonLabels finish reached mark ∧
      HostFrame.Related.Paired (ReturnFrame.Extend older first second) finish reached ∧
      ComparedAllocatorPaths profile ready base bindings leftStart rightStart (leading ++ seen) finish reached offset ∧
      ComparedOccurrencePaths profile ready base bindings start incoming seen finish reached ∧
      OccurrenceTransport profile ready base bindings start incoming ([.tau, .tau, .tau] ++ checkLabels)
        ([.tau, .tau] ++ canonLabels) finish reached [mark] ∧
      pathIndex.Matches checkLabels canonLabels reached ∧
      ∀ pointer cursor, mark = some (.active 0 0) →
        finish.ctl = { cursor with frames := .prog first :: cursor.frames }.control (.pure (.nat pointer)) →
        CollectionRangeCut profile ready base bindings older finish reached cursor destination area entries.length pointer
          (Stored.Endpoints.RecordLower.Field.listObjects entries)
          (fun addr verdict => checkedCollectionTail destination inst entries area index output addr verdict >>= checkNext)
          (fun addr => canonicalCollectionTail destination inst entries area output addr mode >>= canonNext) ∧
        CollectionRangePaths profile ready base bindings leftStart rightStart (leading ++ seen) offset destination area entries
          pointer finish reached cursor (fun issue => checkNext (.error issue)) (LinkedCallback.CollectionVisit.afterAllocation index)
          (canonicalCollectionTail destination inst entries area output pointer mode >>= canonNext) start incoming seen sink ∧
        ∀ bytes, (core3 grow).memSize? finish.store.core destination.memory = some bytes →
          pointer = alignTo pointer area.alignment → pointer + entries.length * area.size ≤ bytes →
          OwnedMemory.Claims.Record.prepare finish.store finish.host.writer (Field.listObjects entries) = .ok () →
          LiveCollectionChildren profile ready base bindings older destination inst type element entries index output checkNext
            canonNext start incoming finish reached pointer bytes cursor (leading ++ seen) seen
            (visit pointer bytes (leading ++ seen)) leftStart rightStart offset

/-- The live dry run before a nested allocation either reaches the typed
checked continuation alone or admits the finite allocator comparison. The
refusal leaves canonical at its original program, before any width read. -/
def LiveCollectionEntry (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (destination : RecordDestination) (inst : InstId) (type element : Stored.TypeOf)
    (entries : List Stored.Endpoints.RecordLower.Field) (index : Nat) (output : Stored.Lower.Output)
    (checkNext : Except Stored.Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (start incoming : Config (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (visit : Nat → Nat → TrailFinish grow sig := fun _ _ _ _ _ _ _ => True)
    (leftStart : Config (core3 grow) (HostState sig) := start)
    (rightStart : Config (core3 grow) (HostState sig) := incoming) (leading : Trace grow sig := []) (offset : Nat := 0)
    (sink : RefusalSink grow sig := .ignore) : Prop :=
  open Stored.Endpoints.RecordLower in
  match OwnedMemory.Claims.Record.prepare start.store start.host.writer (Field.listObjects entries) with
  | .error issue =>
    let refusal := match issue with
      | .preflight reason => Issue.field index (.beforeAllocation reason)
      | reason => Issue.nested index reason
    start.store = incoming.store ∧
    incoming.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) output >>= canonNext) ∧
    let stopped := { start with ctl := check.control (checkNext (.error refusal)) }
    ComparedSlots profile ready base bindings leftStart rightStart leading stopped incoming offset ∧
    ComparedOccurrencePaths profile ready base bindings start incoming [] stopped incoming ∧
    OccurrenceTransport profile ready base bindings start incoming [.tau, .tau] [] stopped incoming ∧
    sink.exit (fun reason => checkNext (.error reason)) refusal leading stopped incoming check
  | .ok () => (core3 grow).memAddrType? incoming.store.core destination.memory = some destination.width →
    LiveCollectionPaths profile ready base bindings older destination inst type element entries index output checkNext canonNext
      start incoming check canon visit leftStart rightStart leading offset sink

/-- A reached collection segment. The slot offset counts removed frames.
On checked refusal, the canonical program is the actual unexecuted suffix
at the reached stop, not necessarily the initial child-entry program. -/
def CollectionSegmentThen (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (checked canonical : Config (core3 grow) (HostState sig))
    (check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) {Result : Type}
    (checkNext : Except Stored.Endpoints.RecordLower.Issue Result → Session grow sig (Ret (core3 grow)))
    (canonNext : Result → Session grow sig (Ret (core3 grow))) (offset : Nat)
    (stopsAt : Session grow sig (Ret (core3 grow)) → Prop)
    (next : Result → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
      PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → Prop) : Prop :=
  let checkedDispatch := specDispatch ready base
  let canonDispatch := specDispatch ready (LiveDispatch.host bindings base)
  ∃ (canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) (outcome : PayloadPrefix.Outcome Result)
    (checkLabels canonLabels : Trace grow sig) (left right : Config (core3 grow) (HostState sig)),
    Steps profile ready checkedDispatch checked checkLabels left ∧ Steps profile ready canonDispatch canonical canonLabels right ∧
    left.store = right.store ∧ PayloadPrefix.visible checkLabels = PayloadPrefix.visible canonLabels ∧
    match outcome with
    | .trapped reason => left.ctl = [] ∧ right.ctl = [] ∧ ∃ leading, PayloadPrefix.visible canonLabels = leading ++ [.trap reason]
    | .returned value => LinkedCallback.ChildFrameOver older left right check canon ∧
        left.ctl = check.control (checkNext (.ok value)) ∧ right.ctl = canon.control (canonNext value) ∧
        (∀ depth, ReturnFrame.Occurrence.Prefix profile ready checkedDispatch checked (.active 0 (depth + offset))
          checkLabels left (.active 0 depth)) ∧
        (∀ depth, ReturnFrame.Occurrence.Prefix profile ready canonDispatch canonical (.active 0 (depth + offset))
          canonLabels right (.active 0 depth)) ∧ next value left right canon
    | .refused issue => ∃ stop, stopsAt stop ∧
        left.ctl = check.control (checkNext (.error issue)) ∧ right.ctl = canon.control stop ∧
        (∀ depth, ReturnFrame.Occurrence.Prefix profile ready checkedDispatch checked (.active 0 (depth + offset))
          checkLabels left (.active 0 depth)) ∧
        (∀ depth, ReturnFrame.Occurrence.Prefix profile ready canonDispatch canonical (.active 0 (depth + offset))
          canonLabels right (.active 0 depth))

abbrev CollectionSegment (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (checked canonical : Config (core3 grow) (HostState sig))
    (check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) {Result : Type}
    (checkNext : Except Stored.Endpoints.RecordLower.Issue Result → Session grow sig (Ret (core3 grow)))
    (canonNext : Result → Session grow sig (Ret (core3 grow))) (offset : Nat)
    (stopsAt : Session grow sig (Ret (core3 grow)) → Prop) (keep : CStore (core3 grow) → Prop := fun _ => True) : Prop :=
  CollectionSegmentThen profile ready base bindings older checked canonical check checkNext canonNext offset stopsAt
    (fun _ left _ _ => keep left.store)

/-- The specialization in which a failed fresh preparation stops before
any child executes. -/
abbrev CollectionReturn (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (checked canonical : Config (core3 grow) (HostState sig))
    (check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) {Result : Type}
    (checkNext : Except Stored.Endpoints.RecordLower.Issue Result → Session grow sig (Ret (core3 grow)))
    (canonNext : Result → Session grow sig (Ret (core3 grow))) (childEntry : Session grow sig (Ret (core3 grow))) : Prop :=
  CollectionSegment profile ready base bindings older checked canonical check checkNext canonNext 1 (· = childEntry)

/-- The unexecuted canonical list suffix at a reached nominal guard. The
address advances by the actual element stride, not by the number of writes. -/
def ElementStop (destination : RecordDestination) (inst : InstId) (entries : List Stored.Endpoints.RecordLower.Field)
    (stride ptr : Nat) (finish : Unit → Session grow sig (Ret (core3 grow))) (stop : Session grow sig (Ret (core3 grow))) : Prop :=
  ∃ leading remaining, entries = leading ++ remaining ∧ remaining ≠ [] ∧
    stop = (Stored.Endpoints.RecordLower.CanonicalTree.elements Limits.spec Quirks.none (destination.context inst)
      destination.width remaining .value stride (ptr + leading.length * stride) >>= finish)

/-- The nominal leaf schemas currently compared by the local collection rule. -/
inductive NominalElement : Stored.TypeOf → Prop where
  | own (resource : RtId) : NominalElement (.own resource)
  | future (element : Async.Element) : NominalElement (.future element)
  | stream (element : Async.Element) : NominalElement (.stream element)
  | context : NominalElement .errorContext

/-- The list depth is a property of the declared type, including empty
lists. It is independent of scheduler or allocator fuel. -/
inductive NominalListType : Nat → Stored.TypeOf → Prop where
  | leaf {type} : NominalElement type → NominalListType 0 type
  | list {depth element} : NominalListType depth element → NominalListType (depth + 1) (.list element)

/-- Visit an allocated list's actual element programs in order. The
continuation for a child admits the next sibling only on common success. -/
def liveElements (destination : RecordDestination) (inst : InstId) (stride : Nat)
    (child : LinkedCallback.MemorySequence.FieldComparison grow sig)
    (checkNext : LinkedCallback.MemorySequence.CheckNext grow sig) (canonNext : LinkedCallback.MemorySequence.CanonNext grow sig)
    (finish : LinkedCallback.MemorySequence.Finish grow sig) :
    List Stored.Endpoints.RecordLower.Field → Nat → Nat → LinkedCallback.MemorySequence.Finish grow sig
  | [], _, _, left, right, check, canon => finish left right check canon
  | item :: rest, index, pointer, left, right, check, canon =>
    open LinkedCallback.MemorySequence in
    child item index pointer left right check canon
      (checkTail (.elements stride) destination inst rest (index + 1) (pointer + stride) checkNext)
      (canonTail (.elements stride) destination inst rest (pointer + stride) canonNext)
      (liveElements destination inst stride child checkNext canonNext finish rest (index + 1) (pointer + stride))

/-- Allocated elements already enter their canonical child at the placed
address. There is no additional per-element width read. -/
def liveElementsPaths (destination : RecordDestination) (inst : InstId) (stride : Nat)
    (child : TrailFieldComparison grow sig) (checkNext : LinkedCallback.MemorySequence.CheckNext grow sig)
    (canonNext : LinkedCallback.MemorySequence.CanonNext grow sig) (finish : TrailFinish grow sig) :
    List Stored.Endpoints.RecordLower.Field → Nat → Nat → TrailFinish grow sig
  | [], _, _, before, left, right, check, canon => finish before left right check canon
  | item :: rest, index, pointer, before, left, right, check, canon =>
    open LinkedCallback.MemorySequence in
    child item index pointer
      (checkTail (.elements stride) destination inst rest (index + 1) (pointer + stride) checkNext)
      (canonTail (.elements stride) destination inst rest (pointer + stride) canonNext)
      (liveElementsPaths destination inst stride child checkNext canonNext finish rest (index + 1) (pointer + stride))
      before left right check canon

/-- The real descriptor program executes only after every element returns.
The two paths share the descriptor result or canonical trap, not an assumed
rollback of either descriptor write. -/
def LiveValueCommit (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig)) (output : Stored.Lower.Output)
    (checkNext : Except Stored.Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (finish : output.Result → LinkedCallback.MemorySequence.Finish grow sig) : LinkedCallback.MemorySequence.Finish grow sig :=
  fun left right check canon =>
  open PayloadPrefix in
  ∃ (store : CStore (core3 grow)) (result : Except TrapReason output.Result) (labels : Trace grow sig),
    let lhs := localLeafEnd left left.host store check.thread check.frames check.rest (fun value => checkNext (.ok value)) result
    let rhs := localLeafEnd right right.host store canon.thread canon.frames canon.rest canonNext result
    LocalLeafLabels result labels ∧
    CoreGrowthSteps profile ready (specDispatch ready base) left labels lhs ∧
    CoreGrowthSteps profile ready (specDispatch ready (LiveDispatch.host bindings base)) right labels rhs ∧
    PairedLeafSteps profile ready (specDispatch ready base) (specDispatch ready (LiveDispatch.host bindings base)) left right labels lhs rhs ∧
    OccurrenceTransport profile ready base bindings left right labels labels lhs rhs ∧
    ∀ value, result = .ok value →
      ReturnFrame.Occurrence.RetainsActiveSlots profile ready (specDispatch ready base) left labels lhs ∧
      ReturnFrame.Occurrence.RetainsActiveSlots profile ready (specDispatch ready (LiveDispatch.host bindings base)) right labels rhs ∧
      finish value lhs rhs check canon

abbrev LiveListPublish := @LiveValueCommit

def liveListTail (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (destination : RecordDestination) (inst : InstId) (element : Stored.TypeOf) (entries : List Stored.Endpoints.RecordLower.Field)
    (index : Nat) (output : Stored.Lower.Output) (compare : LinkedCallback.MemorySequence.FieldComparison grow sig)
    (checkNext : LinkedCallback.MemorySequence.ValueCheckNext grow sig output)
    (canonNext : LinkedCallback.MemorySequence.ValueCanonNext grow sig output)
    (finish : LinkedCallback.MemorySequence.ValueFinish grow sig output) : Nat → Nat → LinkedCallback.MemorySequence.Finish grow sig :=
  open ABI LinkedCallback.MemorySequence in
  fun pointer _ => liveElements destination inst (layout destination.width element).size compare
    (publishChecked destination inst pointer entries.length index output checkNext)
    (publishCanonical destination inst pointer entries.length output canonNext)
    (LiveListPublish profile ready base bindings output checkNext canonNext finish) entries 0 pointer

def liveListTailPaths (destination : RecordDestination) (inst : InstId) (element : Stored.TypeOf)
    (entries : List Stored.Endpoints.RecordLower.Field) (index : Nat) (output : Stored.Lower.Output)
    (child : TrailFieldComparison grow sig)
    (checkNext : LinkedCallback.MemorySequence.ValueCheckNext grow sig output)
    (canonNext : LinkedCallback.MemorySequence.ValueCanonNext grow sig output)
    (publish : TrailFinish grow sig) : Nat → Nat → TrailFinish grow sig :=
  open ABI LinkedCallback.MemorySequence in
  fun pointer _ => liveElementsPaths destination inst (layout destination.width element).size child
    (publishChecked destination inst pointer entries.length index output checkNext)
    (publishCanonical destination inst pointer entries.length output canonNext) publish entries 0 pointer

/-- A decreasing comparison for nested list elements under the two live
dispatchers. Each allocation uses its own occurrence trail and rechecks
the actual reached writer before taking the child branch. -/
def liveNominalList (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId) :
    Nat → LinkedCallback.MemorySequence.FieldComparison grow sig
  | 0 => fun item index address left right check canon checkNext canonNext finish =>
    LinkedCallback.HandleFieldThenBetween profile ready (specDispatch ready base)
      (specDispatch ready (LiveDispatch.host bindings base)) item index (.memory address) left right check canon
      checkNext canonNext (fun () => finish)
  | depth + 1 => fun item index address left right check canon checkNext canonNext finish =>
    open Stored.Endpoints.RecordLower in
    ∃ element entries, item = .dynamic (.list element) element entries ∧
      LiveCollectionEntry profile ready base bindings older destination inst (.list element) element entries index
        (.memory address) checkNext canonNext left right check canon
        (fun pointer bytes _ => liveListTail profile ready base bindings destination inst element entries index (.memory address)
          (liveNominalList profile ready base bindings older destination inst depth) checkNext canonNext (fun () => finish) pointer bytes)

/-- Enter the actual public bodies. The collection visitor sees the
children only at a valid return with a fresh successful reservation. -/
def LinkedCollectionBody (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (type element : Stored.TypeOf)
    (incoming : Config (core3 grow) (HostState sig))
    (visit : Config (core3 grow) (HostState sig) → List Stored.Endpoints.RecordLower.Field → Nat → Nat → TrailFinish grow sig) : Prop :=
  ∃ entries leading entered peer,
    site.field = .dynamic type element entries ∧ PayloadPrefix.visible leading = [] ∧
    (∀ place, ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base))
      incoming place leading entered
      (((ReturnFrame.Occurrence.Edit.push (.core site.core site.resume)).follow place).getD place)) ∧
    entered.host = incoming.host ∧
    LiveCollectionPaths profile ready base bindings older site.destination site.inst type element entries 0
      route.output site.reply site.referenceReply site.checked entered site.cursor peer (visit entered entries)

abbrev LinkedNominalListBody (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (depth : Nat) (element : Stored.TypeOf)
    (incoming : Config (core3 grow) (HostState sig)) : Prop :=
  LinkedCollectionBody profile ready base bindings older site (.list element) element incoming (fun _ entries pointer bytes _ =>
    liveListTail profile ready base bindings site.destination site.inst element entries 0 route.output
      (liveNominalList profile ready base bindings older site.destination site.inst depth)
      site.reply site.referenceReply (fun _ _ _ _ _ => True) pointer bytes)

/-- Stop at fresh preparation or at a reached element; neither executes the
remaining canonical elements or publishes a descriptor. -/
def ListReturnStop (destination : RecordDestination) (inst : InstId) (entries : List Stored.Endpoints.RecordLower.Field)
    (area : ABI.Layout) (output : Stored.Lower.Output) (ptr : Nat)
    (finish : output.Result → Session grow sig (Ret (core3 grow))) (stop : Session grow sig (Ret (core3 grow))) : Prop :=
  stop = (PayloadPrefix.canonicalCollectionTail destination inst entries area output ptr >>= finish) ∨
  ElementStop destination inst entries area.size ptr
    (fun _ => Stored.Endpoints.ListLower.publish (destination.context inst) destination.width ptr entries.length output >>= finish) stop

def mapFieldPlacement (cx : LiftLowerContext (core3 grow))
    (mode : Stored.Endpoints.RecordLower.CanonicalTree.EntryMode)
    (next : AddrType → Session grow sig (Ret (core3 grow))) : Session grow sig (Ret (core3 grow)) :=
  match mode with
  | .value => ptrType cx >>= next
  | .memoryMap width _ _ => next width

def mapValueProgram (destination : RecordDestination) (inst : InstId)
    (mode : Stored.Endpoints.RecordLower.CanonicalTree.EntryMode)
    (value : Stored.Endpoints.RecordLower.Field) (afterKey : Nat)
    (finish : Unit → Session grow sig (Ret (core3 grow))) : Session grow sig (Ret (core3 grow)) :=
  open Stored.Endpoints.RecordLower ABI in
  let cx := destination.context inst
  mapFieldPlacement cx mode fun width =>
    CanonicalTree.field Limits.spec Quirks.none cx destination.width value
      (.memory (alignTo afterKey (layout width value.type).alignment)) >>= finish

def mapKeyBody (destination : RecordDestination) (inst : InstId) (slot : Nat)
    (mode : Stored.Endpoints.RecordLower.CanonicalTree.EntryMode) (key value : Stored.Endpoints.RecordLower.Field)
    (next : LinkedCallback.MemorySequence.CanonNext grow sig) (width : AddrType) : Session grow sig (Ret (core3 grow)) :=
  open Stored.Endpoints.RecordLower ABI in
  let area := layout width key.type
  let address := alignTo slot area.alignment
  CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width key (.memory address) >>=
    fun () => mapValueProgram destination inst mode value (address + area.size) next

/-- The key uses the reached map placement and runs before value placement.
If the value stops at its live guard, the stores in its comparison already
include the key write; the entry is not restarted at the key. -/
def LiveMapEntryThen (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (destination : RecordDestination) (inst : InstId) (mode : Stored.Endpoints.RecordLower.CanonicalTree.EntryMode)
    (key value : Stored.Endpoints.RecordLower.Field) (index slot : Nat)
    (compare : LinkedCallback.MemorySequence.FieldComparison grow sig)
    (checkNext : LinkedCallback.MemorySequence.CheckNext grow sig) (canonNext : LinkedCallback.MemorySequence.CanonNext grow sig)
    (finish : LinkedCallback.MemorySequence.Finish grow sig) : LinkedCallback.MemorySequence.Finish grow sig :=
  open Stored.Endpoints.RecordLower ABI LinkedCallback.MemorySequence PayloadPrefix ReturnFrame.Occurrence in
  fun left right check canon =>
    let checked := specDispatch ready base
    let canonical := specDispatch ready (LiveDispatch.host bindings base)
    let cx := destination.context inst
    let keyArea := layout destination.width key.type
    let afterKey := alignTo slot keyArea.alignment + keyArea.size
    let valPtr := alignTo afterKey (layout destination.width value.type).alignment
    let report := aggregateNext index checkNext
    let valCheck := fun () => Record.Effects.field recordClaims Limits.spec Quirks.none cx destination.width value 1 (.memory valPtr) >>= report
    let valCanon := fun () => mapValueProgram destination inst mode value afterKey canonNext
    let atKey := { right with ctl := canon.control (mapKeyBody destination inst slot mode key value canonNext destination.width) }
    ∃ keyRead, visible keyRead = [] ∧ (∀ place, Prefix profile ready canonical right place keyRead atKey place) ∧
    ∃ (store : CStore (core3 grow)) (result : Except TrapReason Unit) (checkLabels canonLabels : Trace grow sig),
      let lhs := localLeafEnd left left.host store check.thread check.frames check.rest valCheck result
      let rhs := localLeafEnd atKey right.host store canon.thread canon.frames canon.rest valCanon result
      Steps profile ready checked left checkLabels lhs ∧ LocalSteps profile ready canonical atKey canonLabels rhs ∧
      visible checkLabels = visible canonLabels ∧
      OccurrenceTransport profile ready base bindings left atKey checkLabels canonLabels lhs rhs ∧
      match result with
      | .error reason => ∃ leading, visible canonLabels = leading ++ [.trap reason]
      | .ok () =>
        let atValue := { rhs with ctl := canon.control (CanonicalTree.field Limits.spec Quirks.none cx destination.width value
          (.memory valPtr) >>= canonNext) }
        RetainsActiveSlots profile ready checked left checkLabels lhs ∧
        RetainsActiveSlots profile ready canonical atKey canonLabels rhs ∧
        ∃ valueRead, visible valueRead = [] ∧ (∀ place, Prefix profile ready canonical rhs place valueRead atValue place) ∧
          compare value 1 valPtr lhs atValue check canon report canonNext finish

abbrev MapEntryComparison (grow : SingleThreaded.GrowOracle) (sig : Signature) :=
  Stored.Endpoints.RecordLower.Field → Stored.Endpoints.RecordLower.Field → Nat → Nat →
    LinkedCallback.MemorySequence.FieldComparison grow sig → LinkedCallback.MemorySequence.CheckNext grow sig →
    LinkedCallback.MemorySequence.CanonNext grow sig → LinkedCallback.MemorySequence.Finish grow sig →
    LinkedCallback.MemorySequence.Finish grow sig

def liveMapElementsWith (entry : MapEntryComparison grow sig)
    (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType) (element : Stored.TypeOf)
    (output : Stored.Lower.Output) (compare : LinkedCallback.MemorySequence.FieldComparison grow sig)
    (checkNext : LinkedCallback.MemorySequence.CheckNext grow sig) (canonNext : LinkedCallback.MemorySequence.CanonNext grow sig)
    (finish : LinkedCallback.MemorySequence.Finish grow sig) :
    List Stored.Endpoints.RecordLower.Field → Nat → Nat → LinkedCallback.MemorySequence.Finish grow sig
  | [], _, _, left, right, check, canon => finish left right check canon
  | item :: rest, index, pointer, left, right, check, canon =>
    open Stored.Endpoints.RecordLower ABI LinkedCallback.MemorySequence in
    let entryType : Stored.TypeOf := .record (mapEntryFields key element)
    let stride := (layout destination.width entryType).size
    let mode := CanonicalTree.EntryMode.forOutput destination.width (.map key element) output
    ∃ (payload : Stored.Payload (.prim key.toPrimitive)) (value : Field),
      let keyField := Field.data (.prim key.toPrimitive) payload
      item = .aggregate entryType [keyField, value] ∧
      entry keyField value index pointer compare
        (checkTail (.elements stride) destination inst rest (index + 1) (pointer + stride) checkNext)
        (fun () => CanonicalTree.elements Limits.spec Quirks.none (destination.context inst) destination.width
          rest mode stride (pointer + stride) >>= canonNext)
        (liveMapElementsWith entry destination inst key element output compare checkNext canonNext finish
          rest (index + 1) (pointer + stride)) left right check canon

def liveMapTailWith (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (entry : MapEntryComparison grow sig)
    (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType) (element : Stored.TypeOf)
    (entries : List Stored.Endpoints.RecordLower.Field) (index : Nat) (output : Stored.Lower.Output)
    (compare : LinkedCallback.MemorySequence.FieldComparison grow sig)
    (checkNext : LinkedCallback.MemorySequence.ValueCheckNext grow sig output)
    (canonNext : LinkedCallback.MemorySequence.ValueCanonNext grow sig output)
    (finish : LinkedCallback.MemorySequence.ValueFinish grow sig output) : Nat → Nat → LinkedCallback.MemorySequence.Finish grow sig :=
  open LinkedCallback.MemorySequence in
  fun pointer _ => liveMapElementsWith entry destination inst key element output compare
    (publishChecked destination inst pointer entries.length index output checkNext)
    (publishCanonical destination inst pointer entries.length output canonNext)
    (LiveListPublish profile ready base bindings output checkNext canonNext finish) entries 0 pointer

abbrev liveMapTail (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType) (element : Stored.TypeOf)
    (entries : List Stored.Endpoints.RecordLower.Field) (index : Nat) (output : Stored.Lower.Output) :=
  liveMapTailWith profile ready base bindings
    (LiveMapEntryThen profile ready base bindings destination inst
      (Stored.Endpoints.RecordLower.CanonicalTree.EntryMode.forOutput destination.width (.map key element) output))
    destination inst key element entries index output

abbrev LinkedMapListBody (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (key : WIT.KeyType) (depth : Nat) (element : Stored.TypeOf)
    (incoming : Config (core3 grow) (HostState sig)) : Prop :=
  LinkedCollectionBody profile ready base bindings older site (.map key element) (.record (ABI.mapEntryFields key element)) incoming
    (fun _ entries pointer bytes _ => liveMapTail profile ready base bindings site.destination site.inst key element entries 0 route.output
      (liveNominalList profile ready base bindings older site.destination site.inst depth)
      site.reply site.referenceReply (fun _ _ _ _ _ => True) pointer bytes)

/-- The current proof fragment, not the runtime support predicate. -/
inductive RecursiveCollectionType : Stored.TypeOf → Prop where
  | leaf {type} : NominalElement type → RecursiveCollectionType type
  | data {type} : PayloadPrefix.LocalDataType type → RecursiveCollectionType type
  | string : RecursiveCollectionType (.prim .string)
  | list {element} : RecursiveCollectionType element → RecursiveCollectionType (.list element)
  | fixed {element length} : RecursiveCollectionType element → RecursiveCollectionType (.fixedList element length)
  | map {key element} : RecursiveCollectionType element → RecursiveCollectionType (.map key element)
  | option {element} : RecursiveCollectionType element → RecursiveCollectionType (.option element)
  | result {success failure} : (∀ type, success = some type → RecursiveCollectionType type) →
      (∀ type, failure = some type → RecursiveCollectionType type) → RecursiveCollectionType (.result success failure)
  | variant {cases : List (String × Option Stored.TypeOf)} :
      (∀ name type, (name, some type) ∈ cases → RecursiveCollectionType type) → RecursiveCollectionType (.variant cases)
  | record {fields : List (String × Stored.TypeOf)} :
      (∀ name type, (name, type) ∈ fields → RecursiveCollectionType type) → RecursiveCollectionType (.record fields)
  | tuple {types : List Stored.TypeOf} :
      (∀ type, type ∈ types → RecursiveCollectionType type) → RecursiveCollectionType (.tuple types)

def CollectionRoot : Stored.TypeOf → Prop
  | .list _ | .map .. => True
  | _ => False

/-- Record either a canonical trap at the reached stores or a continuing
cursor pair with its original occurrences. Local completion does not choose
or run a later sibling. -/
def LocalPathsThen (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (start incoming : Config (core3 grow) (HostState sig)) (seen : Trace grow sig) (offset : Nat)
    (finish : Trace grow sig → LinkedCallback.MemorySequence.Finish grow sig) : Prop :=
  (∃ reason leading lhs rhs,
    ComparedPaths profile ready base bindings start incoming (seen ++ (leading ++ [.trap reason])) lhs rhs ∧
    lhs.ctl = [] ∧ rhs.ctl = []) ∨
  (∃ more lhs rhs check canon,
    ComparedSlots profile ready base bindings start incoming (seen ++ more) lhs rhs offset ∧
    lhs.store = rhs.store ∧ finish (seen ++ more) lhs rhs check canon)

/-- A local field or flat coercion suffix with exact all-location paths from
its reached entry. These can be rebased even when an older occurrence is
saved or was lost before this cut. -/
def LocatedLocalPathsThen (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (start incoming left right : Config (core3 grow) (HostState sig)) (seen : Trace grow sig) (offset : Nat)
    (finish : Trace grow sig → LinkedCallback.MemorySequence.Finish grow sig) : Prop :=
  (∃ reason leading lhs rhs,
    ComparedPaths profile ready base bindings start incoming (seen ++ (leading ++ [.trap reason])) lhs rhs ∧
    ComparedOccurrencePaths profile ready base bindings left right (leading ++ [.trap reason]) lhs rhs ∧
    lhs.ctl = [] ∧ rhs.ctl = []) ∨
  (∃ more lhs rhs check canon,
    ComparedSlots profile ready base bindings start incoming (seen ++ more) lhs rhs offset ∧
    ComparedOccurrencePaths profile ready base bindings left right more lhs rhs ∧
    finish (seen ++ more) lhs rhs check canon)

/-- A typed live refusal advances only the checked guard; the canonical
cursor remains at the unexecuted field. Otherwise compare the reached stores
and continue only on success. -/
def HandlePathsThen (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (start incoming : Config (core3 grow) (HostState sig)) (seen : Trace grow sig) (offset : Nat)
    (item : Stored.Endpoints.RecordLower.Field) (index : Nat)
    {Result : Type} (checkNext : Except Stored.Endpoints.RecordLower.Issue Result → Session grow sig (Ret (core3 grow)))
    (finish : Trace grow sig → LinkedCallback.MemorySequence.Finish grow sig)
    (left right : Config (core3 grow) (HostState sig))
    (check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) (sink : RefusalSink grow sig := .ignore) : Prop :=
  (∃ issue, liveLeafPlan left.store left.host.writer index item = .error issue ∧
    let refused := { left with ctl := check.control (checkNext (.error issue)) }
    ComparedSlots profile ready base bindings start incoming seen refused right offset ∧
      ComparedOccurrencePaths profile ready base bindings left right [] refused right ∧
      sink.exit (fun reason => checkNext (.error reason)) issue seen refused right check) ∨
  LocatedLocalPathsThen profile ready base bindings start incoming left right seen offset finish

/-- A reached map key under the live dispatchers, from field placement
through the recursive string plan. Only completed plans reach the supplied
descriptor continuation. -/
def StringValueThen (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (destination : RecordDestination) (inst : InstId)
    (key : LinkedCallback.StringField) (output : Stored.Lower.Output)
    (left right : Config (core3 grow) (HostState sig)) (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (checkNext : LinkedCallback.MemorySequence.ValueCheckNext grow sig output)
    (canonNext : LinkedCallback.MemorySequence.ValueCanonNext grow sig output)
    (finish : Nat → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
      PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → Prop) : Prop :=
  let cx := destination.context inst
  let plan := storePlanFor Quirks.none destination.encoding destination.width key.value
  let checked := fun pointer => PayloadPrefix.stringPlanTail cx destination.width output plan pointer >>=
    fun result => checkNext (.ok result)
  let canonical := fun pointer => PayloadPrefix.stringPlanTail cx destination.width output plan pointer >>= canonNext
  let checkBody := { left with ctl := check.control (runStoreSteps cx 0 plan.steps >>= checked) }
  let canonBody := { right with ctl := canon.control (runStoreSteps cx 0 plan.steps >>= canonical) }
  ∃ checkLabels canonLabels,
    PayloadPrefix.visible checkLabels = [] ∧ PayloadPrefix.visible canonLabels = [] ∧
    (∀ place, ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready base) left place checkLabels checkBody place) ∧
    (∀ place, ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base))
      right place canonLabels canonBody place) ∧
    PayloadPrefix.SilentLocalPath profile ready (specDispatch ready base) left checkLabels checkBody ∧
    PayloadPrefix.SilentLocalPath profile ready (specDispatch ready (LiveDispatch.host bindings base)) right canonLabels canonBody ∧
    LinkedCallback.ChildFrameOver older checkBody canonBody check canon ∧
    LiveStringReplay profile ready base bindings older cx checked canonical finish plan.steps.length checkBody canonBody check canon

abbrev StringKeyThen (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (destination : RecordDestination) (inst : InstId) (key : LinkedCallback.StringField) (address : Nat) :=
  StringValueThen profile ready base bindings older destination inst key (.memory address)

/-- The same string field along a cumulative occurrence path, including each
finite allocator prefix and the selected output continuation after actual return. -/
def StringValuePaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (destination : RecordDestination) (inst : InstId) (key : LinkedCallback.StringField) (output : Stored.Lower.Output)
    (start incoming left right : Config (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (checkNext : LinkedCallback.MemorySequence.ValueCheckNext grow sig output)
    (canonNext : LinkedCallback.MemorySequence.ValueCanonNext grow sig output)
    (finish : Nat → Trace grow sig → LinkedCallback.MemorySequence.Finish grow sig) (seen : Trace grow sig) (offset : Nat) : Prop :=
  let cx := destination.context inst
  let plan := storePlanFor Quirks.none destination.encoding destination.width key.value
  let checked := fun pointer => PayloadPrefix.stringPlanTail cx destination.width output plan pointer >>=
    fun result => checkNext (.ok result)
  let canonical := fun pointer => PayloadPrefix.stringPlanTail cx destination.width output plan pointer >>= canonNext
  let checkBody := { left with ctl := check.control (runStoreSteps cx 0 plan.steps >>= checked) }
  let canonBody := { right with ctl := canon.control (runStoreSteps cx 0 plan.steps >>= canonical) }
  LiveStringPaths profile ready base bindings older cx checked canonical start incoming
    (fun pointer lhs rhs check canon observed => finish pointer observed lhs rhs check canon)
    plan.steps.length checkBody canonBody check canon seen offset

/-- Follow every initial occurrence from the incoming field through the real
entry guards and the reached string plan, including finite allocator cuts. -/
def StringValueOccurrencePaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (destination : RecordDestination) (inst : InstId) (key : LinkedCallback.StringField) (output : Stored.Lower.Output)
    (start incoming left right : Config (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (checkNext : LinkedCallback.MemorySequence.ValueCheckNext grow sig output)
    (canonNext : LinkedCallback.MemorySequence.ValueCanonNext grow sig output)
    (finish : Nat → Trace grow sig → LinkedCallback.MemorySequence.Finish grow sig) (seen : Trace grow sig)
    (leftBody : Config (core3 grow) (HostState sig) := left) (rightBody : Config (core3 grow) (HostState sig) := right) : Prop :=
  let cx := destination.context inst
  let plan := storePlanFor Quirks.none destination.encoding destination.width key.value
  let checked := fun pointer => PayloadPrefix.stringPlanTail cx destination.width output plan pointer >>=
    fun result => checkNext (.ok result)
  let canonical := fun pointer => PayloadPrefix.stringPlanTail cx destination.width output plan pointer >>= canonNext
  let checkBody := { left with ctl := check.control (runStoreSteps cx 0 plan.steps >>= checked) }
  let canonBody := { right with ctl := canon.control (runStoreSteps cx 0 plan.steps >>= canonical) }
  LiveStringOccurrences profile ready base bindings older cx checked canonical start incoming finish
    plan.steps.length checkBody canonBody check canon seen leftBody rightBody

abbrev StringKeyPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (destination : RecordDestination) (inst : InstId) (key : LinkedCallback.StringField) (address : Nat) :=
  StringValuePaths profile ready base bindings older destination inst key (.memory address)

def flatWordVisit (finish : FlatTrailFinish grow sig) : TrailFinish grow sig :=
  fun seen lhs rhs check canon => ∃ words, finish words seen lhs rhs check canon

def selectFlatPaths (paths : List (Stored.TypeOf × FlatFieldTrail grow sig)) : FlatFieldTrail grow sig :=
  fun item index checkNext canonNext finish before left right check canon =>
    ∃ child, (item.type, child) ∈ paths ∧ child item index checkNext canonNext finish before left right check canon

def flatAggregatePaths (destination : RecordDestination) (inst : InstId) (child : FlatFieldTrail grow sig) :
    FlatFieldTrail grow sig :=
  fun item index checkNext canonNext finish before left right check canon =>
    open Stored.Endpoints.RecordLower in
    ∃ children, LinkedCallback.flatChildren item = some children ∧
      flatSequencePaths destination inst child (fun verdict => checkNext (verdict.mapError (.nested index)))
        canonNext finish children 0 [] before left right check canon

def noFlatChild : FlatFieldTrail grow sig := fun _ _ _ _ _ _ _ _ _ _ => False

/-- The selected arm runs before the flat tag and coercion tail; the actual
checked error continuation skips that tail. -/
def flatSumPathsWith (tail : TrailFinish grow sig → TrailFinish grow sig) (width : AddrType) (type : Stored.TypeOf) (arms : List (Option Stored.TypeOf))
    (pick : Nat → FlatFieldTrail grow sig) : FlatFieldTrail grow sig :=
  fun item index checkNext canonNext finish before left right check canon =>
    open LinkedCallback ABI in
    ∃ tag selected, item = .sum type arms tag selected ∧
      match selected with
      | none => tail (flatWordVisit finish) before left right check canon
      | some child =>
        let haves := flatten width child.type
        pick tag child 0 (flatSumCheckNext width type arms.length tag index haves checkNext)
          (fun words => flatSumTail width type arms.length tag haves words >>= canonNext)
          (fun _ => tail (flatWordVisit finish))
          before left right check canon

abbrev TrailLeafType (type : Stored.TypeOf) : Prop :=
  NominalElement type ∨ PayloadPrefix.LocalDataType type ∨ type = .prim .string

abbrev flatSumPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (start incoming : Config (core3 grow) (HostState sig)) (offset : Nat)
    (width : AddrType) (type : Stored.TypeOf) (arms : List (Option Stored.TypeOf))
    (pick : Nat → FlatFieldTrail grow sig) : FlatFieldTrail grow sig :=
  flatSumPathsWith (fun visit seen lhs rhs _ _ => LocatedLocalPathsThen profile ready base bindings start incoming lhs rhs seen offset visit)
    width type arms pick

/-- The trail comparison for the leaf cases of the compiled field visitor.
The corresponding theorem restricts this view to the certified leaf schemas. -/
def liveLeafPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (offset : Nat) (sink : RefusalSink grow sig := .ignore) :
    Stored.TypeOf → TrailFieldComparison grow sig
  | .prim .string => fun item _ address checkNext canonNext finish before left right check canon =>
    ∃ str : LinkedCallback.StringField, item = str.field ∧
      StringKeyPaths profile ready base bindings older destination inst str address start incoming left right check canon
        checkNext canonNext (fun _ observed lhs rhs _ _ =>
          LocatedLocalPathsThen profile ready base bindings start incoming lhs rhs observed offset finish)
        before offset
  | .prim _ | .enum _ | .flags _ => fun _ _ _ _ _ finish before left right _ _ =>
    LocatedLocalPathsThen profile ready base bindings start incoming left right before offset finish
  | _ => fun item index _ checkNext _ finish before left right check _ =>
    HandlePathsThen profile ready base bindings start incoming before offset item index checkNext finish left right check sink

/-- At a closed leaf, retain the exact cumulative trap or feed the reached
return into the surrounding visitor. -/
def LocalOccurrenceThen (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (start incoming : Config (core3 grow) (HostState sig)) (seen : Trace grow sig) (finish : TrailFinish grow sig) : Prop :=
  (∃ reason leading lhs rhs,
    ComparedOccurrencePaths profile ready base bindings start incoming (seen ++ (leading ++ [.trap reason])) lhs rhs ∧
    lhs.ctl = [] ∧ rhs.ctl = []) ∨
  (∃ more lhs rhs check canon,
    ComparedOccurrencePaths profile ready base bindings start incoming (seen ++ more) lhs rhs ∧
    finish (seen ++ more) lhs rhs check canon)

/-- A local operation either reaches a common trap or passes its augmented
history to the next actual continuation. -/
def LocalTransportThen (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (start incoming : Config (core3 grow) (HostState sig)) (seen : Trace grow sig) (finish : TrailFinish grow sig) : Prop :=
  (∃ reason leading lhs rhs,
    ComparedOccurrenceTransport profile ready base bindings start incoming (seen ++ (leading ++ [.trap reason])) lhs rhs ∧
    lhs.ctl = [] ∧ rhs.ctl = []) ∨
  (∃ more lhs rhs check canon,
    ComparedOccurrenceTransport profile ready base bindings start incoming (seen ++ more) lhs rhs ∧
    finish (seen ++ more) lhs rhs check canon)

/-- A nominal guard can stop the checked field without running the
canonical leaf or any sibling. The occurrence history ends at that pair. -/
def HandleOccurrenceThen (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (start incoming left right : Config (core3 grow) (HostState sig)) (seen : Trace grow sig)
    (item : Stored.Endpoints.RecordLower.Field) (index : Nat) {Result : Type}
    (check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except Stored.Endpoints.RecordLower.Issue Result → Session grow sig (Ret (core3 grow)))
    (finish : TrailFinish grow sig) (sink : RefusalSink grow sig) : Prop :=
  (∃ issue, liveLeafPlan left.store left.host.writer index item = .error issue ∧
    let refused := { left with ctl := check.control (checkNext (.error issue)) }
    ComparedOccurrencePaths profile ready base bindings start incoming seen refused right ∧
    sink.exit (fun reason => checkNext (.error reason)) issue seen refused right check) ∨
  LocalOccurrenceThen profile ready base bindings start incoming seen finish

def RefusalSink.CoversOccurrences (sink : RefusalSink grow sig) (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (start incoming : Config (core3 grow) (HostState sig)) : Prop :=
  ∀ next, sink.admits next → ∀ issue seen left right check,
    left.ctl = check.control (next issue) →
    ComparedOccurrencePaths profile ready base bindings start incoming seen left right → sink.exit next issue seen left right check

/-- The nominal guard's one-sided advance has a concrete checked trail
and an empty canonical trail. Success or a common trap uses the reached
spent writer, not the original authority. -/
def HandleTransportThen (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (start incoming left right : Config (core3 grow) (HostState sig)) (seen : Trace grow sig)
    (item : Stored.Endpoints.RecordLower.Field) (index : Nat) {Result : Type}
    (check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except Stored.Endpoints.RecordLower.Issue Result → Session grow sig (Ret (core3 grow)))
    (finish : TrailFinish grow sig) (sink : RefusalSink grow sig) : Prop :=
  (∃ issue, liveLeafPlan left.store left.host.writer index item = .error issue ∧
    let refused := { left with ctl := check.control (checkNext (.error issue)) }
    ComparedOccurrenceTransport profile ready base bindings start incoming seen refused right ∧
    sink.exit (fun reason => checkNext (.error reason)) issue seen refused right check) ∨
  LocalTransportThen profile ready base bindings start incoming seen finish

/-- The range branch of the actual marked return. Misalignment and bounds
traps retain the reached prefix. A fresh reservation failure stops canonical
before the child program, and only a successful reservation enters it. -/
def CollectionOccurrenceRangeThen (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (origin : CStore (core3 grow))
    (start incoming leftEntry rightEntry checked canonical : Config (core3 grow) (HostState sig)) (seen localSeen : Trace grow sig)
    (destination : RecordDestination) (area : ABI.Layout) (entries : List Stored.Endpoints.RecordLower.Field)
    (pointer : Nat) (check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (refuse : IssueProgram grow sig) (wrap : Stored.Endpoints.RecordLower.Issue → Stored.Endpoints.RecordLower.Issue)
    (checkedChildren canonicalChildren : Session grow sig (Ret (core3 grow)))
    (visit : Nat → TrailFinish grow sig) (sink : RefusalSink grow sig) : Prop :=
  open Stored.Endpoints.RecordLower in
  let trap := fun reason => ComparedOccurrencePaths profile ready base bindings start incoming (seen ++ [.trap reason])
    (StepDefs.trapCfg checked) (StepDefs.trapCfg canonical) ∧
    ComparedOccurrenceTransport profile ready base bindings leftEntry rightEntry (localSeen ++ [.trap reason])
      (StepDefs.trapCfg checked) (StepDefs.trapCfg canonical)
  ∃ bytes, (core3 grow).memSize? checked.store.core destination.memory = some bytes ∧
    if pointer ≠ ABI.alignTo pointer area.alignment then trap .unalignedPointer
    else if pointer + entries.length * area.size ≤ bytes then
      (∀ issue, OwnedMemory.Claims.Record.prepare checked.store checked.host.writer (Field.listObjects entries) = .error issue →
        ∃ canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig),
          let stopped := { checked with ctl := check.control (refuse (wrap issue)) }
          let reference := { canonical with ctl := canon.control canonicalChildren }
          ComparedOccurrencePaths profile ready base bindings start incoming seen stopped reference ∧
          ComparedOccurrenceTransport profile ready base bindings leftEntry rightEntry localSeen stopped reference ∧
          sink.exit refuse (wrap issue) seen stopped reference check) ∧
      (OwnedMemory.Claims.Record.prepare checked.store checked.host.writer (Field.listObjects entries) = .ok () →
        ∃ left right canon, ComparedOccurrencePaths profile ready base bindings start incoming seen left right ∧
          ComparedOccurrenceTransport profile ready base bindings leftEntry rightEntry localSeen left right ∧
          LinkedCallback.ChildFrameOver older left right check canon ∧
          (core3 grow).memAddrType? left.store.core destination.memory = some destination.width ∧
          (core3 grow).memSize? left.store.core destination.memory = some bytes ∧
          Core3.Grows origin.core left.store.core ∧
          left.ctl = check.control checkedChildren ∧ right.ctl = canon.control canonicalChildren ∧
          CollectionRangeTransport profile ready base bindings checked canonical left right [] ∧
          visit bytes seen left right check canon)
    else trap .outOfBounds

/-- Rebase an actual dynamic field at the reached occurrence coordinates.
Every classified finite allocator prefix is compared, but only the return
of the installed occurrence admits the range branch. -/
def LiveCollectionOccurrenceEntry (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (destination : RecordDestination) (inst : InstId) (type element : Stored.TypeOf)
    (entries : List Stored.Endpoints.RecordLower.Field) (index : Nat) (output : Stored.Lower.Output)
    (checkNext : LinkedCallback.MemorySequence.ValueCheckNext grow sig output)
    (canonNext : LinkedCallback.MemorySequence.ValueCanonNext grow sig output)
    (start incoming left right : Config (core3 grow) (HostState sig)) (before : Trace grow sig)
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (visit : Nat → Nat → TrailFinish grow sig) (sink : RefusalSink grow sig) : Prop :=
  open Stored.Endpoints.RecordLower ABI PayloadPrefix in
  match OwnedMemory.Claims.Record.prepare left.store left.host.writer (Field.listObjects entries) with
  | .error issue =>
    let refusal := match issue with
      | .preflight reason => Issue.field index (.beforeAllocation reason)
      | reason => Issue.nested index reason
    let stopped := { left with ctl := check.control (checkNext (.error refusal)) }
    ComparedOccurrencePaths profile ready base bindings start incoming before stopped right ∧
    OccurrenceTransport profile ready base bindings left right [.tau, .tau] [] stopped right ∧
    sink.exit (fun reason => checkNext (.error reason)) refusal before stopped right check
  | .ok () =>
    let area := layout destination.width element
    let mode := CanonicalTree.EntryMode.forOutput destination.width type output
    let first := checkedCollectionResume destination inst entries area index output checkNext
    let second := canonicalCollectionResume destination inst entries area output canonNext mode
    let leftEntry := collectionEntry destination inst area entries.length (specDispatch ready base) left check first
    let rightEntry := collectionEntry destination inst area entries.length (specDispatch ready (LiveDispatch.host bindings base))
      right canon second
    (core3 grow).memAddrType? right.store.core destination.memory = some destination.width →
    PairedAllocatorInstall profile ready base bindings older first second left right leftEntry rightEntry 3 2 ∧
    ∀ {pathIndex seen finish}, AllocatorCallbackPrefix profile ready base bindings older first second leftEntry rightEntry pathIndex seen finish →
      ∃ checkLabels canonLabels reached mark,
        AllocatorMark profile ready base bindings older leftEntry rightEntry checkLabels canonLabels finish reached mark ∧
        HostFrame.Related.Paired (ReturnFrame.Extend older first second) finish reached ∧
        ComparedOccurrencePaths profile ready base bindings start incoming (before ++ seen) finish reached ∧
        OccurrenceTransport profile ready base bindings left right ([.tau, .tau, .tau] ++ checkLabels)
          ([.tau, .tau] ++ canonLabels) finish reached [mark] ∧
        pathIndex.Matches checkLabels canonLabels reached ∧
        ∀ pointer cursor, mark = some (.active 0 0) →
          finish.ctl = { cursor with frames := .prog first :: cursor.frames }.control (.pure (.nat pointer)) →
          CollectionOccurrenceRangeThen profile ready base bindings older left.store start incoming left right finish reached (before ++ seen) seen
            destination area entries pointer cursor (fun issue => checkNext (.error issue))
            (LinkedCallback.CollectionVisit.afterAllocation index)
            (checkedCollectionTail destination inst entries area index output pointer (.ok ()) >>= checkNext)
            (canonicalCollectionTail destination inst entries area output pointer mode >>= canonNext) (visit pointer) sink

/-- Actual memory leaves, including a string's reached descriptor write
and the nominal leaf's one-sided guard stop. -/
def leafOccurrencePaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (sink : RefusalSink grow sig) : Stored.TypeOf → TrailFieldComparison grow sig
  | .prim .string => fun item _ address checkNext canonNext finish seen left right check canon =>
    ∃ str : LinkedCallback.StringField, item = str.field ∧
      StringValueOccurrencePaths profile ready base bindings older destination inst str (.memory address)
        start incoming left right check canon checkNext canonNext
        (fun _ observed _ _ _ _ => LocalOccurrenceThen profile ready base bindings start incoming observed finish) seen
  | .prim _ | .enum _ | .flags _ => fun _ _ _ _ _ finish seen _ _ _ _ =>
    LocalOccurrenceThen profile ready base bindings start incoming seen finish
  | _ => fun item index _ checkNext _ finish seen left right check _ =>
    HandleOccurrenceThen profile ready base bindings start incoming left right seen item index check checkNext finish sink

abbrev StringKeyReplay (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (origin : CStore (core3 grow)) (destination : RecordDestination) (inst : InstId)
    (key : LinkedCallback.StringField) (address : Nat)
    (left right : Config (core3 grow) (HostState sig)) (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except Stored.Endpoints.RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Unit → Session grow sig (Ret (core3 grow))) : Prop :=
  StringKeyThen profile ready base bindings older destination inst key address left right check canon checkNext canonNext
    (fun _ lhs rhs cursor peer =>
      LinkedCallback.ChildFrameOver older lhs rhs cursor peer ∧ Core3.Grows origin.core lhs.store.core ∧
      PayloadPrefix.StringLocalCutBetween profile ready (specDispatch ready base)
        (specDispatch ready (LiveDispatch.host bindings base)) lhs rhs cursor peer
        (fun result => checkNext (.ok result)) canonNext true)

/-- A string-key plan may suspend. Its actual descriptor writes must finish
before entering the value at the reached map slot. -/
def LiveStringMapEntryThen (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (destination : RecordDestination) (inst : InstId) (element : Stored.TypeOf)
    (output : Stored.Lower.Output) : MapEntryComparison grow sig :=
  open Stored.Endpoints.RecordLower ABI LinkedCallback.MemorySequence PayloadPrefix ReturnFrame.Occurrence in
  fun field value index slot compare checkNext canonNext finish left right check canon =>
    ∃ key : LinkedCallback.StringField, field = key.field ∧
      let cx := destination.context inst
      let mode := CanonicalTree.EntryMode.forOutput destination.width (.map .string element) output
      let keyArea := layout destination.width key.field.type
      let address := alignTo slot keyArea.alignment
      let afterKey := address + keyArea.size
      let valuePtr := alignTo afterKey (layout destination.width value.type).alignment
      let report := aggregateNext index checkNext
      let checked := fun verdict : Except Stored.Endpoints.RecordLower.Issue Unit => (match verdict with
        | .error issue => pure (.error issue)
        | .ok () => Record.Effects.field recordClaims Limits.spec Quirks.none cx destination.width value 1 (.memory valuePtr)) >>= report
      let canonical := fun () => mapValueProgram destination inst mode value afterKey canonNext
      StringKeyThen profile ready base bindings older destination inst key address left right check canon checked canonical
        (fun _ lhs rhs cursor peer =>
          let checkDispatch := specDispatch ready base
          let canonDispatch := specDispatch ready (LiveDispatch.host bindings base)
          ∃ (store : CStore (core3 grow)) (result : Except TrapReason Unit) (labels : Trace grow sig),
            let checkEnd := localLeafEnd lhs lhs.host store cursor.thread cursor.frames cursor.rest (fun res => checked (.ok res)) result
            let canonEnd := localLeafEnd rhs rhs.host store peer.thread peer.frames peer.rest canonical result
            LocalLeafLabels result labels ∧ CoreGrowthSteps profile ready checkDispatch lhs labels checkEnd ∧
            CoreGrowthSteps profile ready canonDispatch rhs labels canonEnd ∧
            OccurrenceTransport profile ready base bindings lhs rhs labels labels checkEnd canonEnd ∧
            match result with
            | .error _ => True
            | .ok () =>
              RetainsActiveSlots profile ready checkDispatch lhs labels checkEnd ∧
              RetainsActiveSlots profile ready canonDispatch rhs labels canonEnd ∧
              let atValue := { canonEnd with ctl := peer.control (CanonicalTree.field Limits.spec Quirks.none cx
                destination.width value (.memory valuePtr) >>= canonNext) }
              ∃ widthRead, visible widthRead = [] ∧ (∀ place, Prefix profile ready canonDispatch canonEnd place widthRead atValue place) ∧
                compare value 1 valuePtr checkEnd atValue cursor peer report canonNext finish)

/-- Track a string-key entry from the original caller pair through key
allocation, descriptor stores and the canonical width read. The value is
entered only after all three have completed. -/
def LiveStringMapEntryPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (destination : RecordDestination) (inst : InstId) (element : Stored.TypeOf)
    (output : Stored.Lower.Output) (start incoming : Config (core3 grow) (HostState sig))
    (seen : Trace grow sig) (offset : Nat) (field value : Stored.Endpoints.RecordLower.Field) (index slot : Nat)
    (checkNext : LinkedCallback.MemorySequence.CheckNext grow sig) (canonNext : LinkedCallback.MemorySequence.CanonNext grow sig)
    (visit : Nat → TrailFinish grow sig)
    (left right : Config (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) : Prop :=
  open Stored.Endpoints.RecordLower ABI LinkedCallback.MemorySequence in
  ∃ key : LinkedCallback.StringField, field = key.field ∧
    let cx := destination.context inst
    let mode := CanonicalTree.EntryMode.forOutput destination.width (.map .string element) output
    let keyArea := layout destination.width key.field.type
    let address := alignTo slot keyArea.alignment
    let afterKey := address + keyArea.size
    let valuePtr := alignTo afterKey (layout destination.width value.type).alignment
    let report := aggregateNext index checkNext
    let checked := fun verdict : Except Stored.Endpoints.RecordLower.Issue Unit => (match verdict with
      | .error issue => pure (.error issue)
      | .ok () => Record.Effects.field recordClaims Limits.spec Quirks.none cx destination.width value 1 (.memory valuePtr)) >>= report
    let canonical := fun () => mapValueProgram destination inst mode value afterKey canonNext
    StringKeyPaths profile ready base bindings older destination inst key address start incoming left right check canon
      checked canonical (fun _ observed _ _ _ _ => LocalPathsThen profile ready base bindings start incoming observed offset (visit valuePtr))
      seen offset

def liveCollectionMapEntry (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType) (element : Stored.TypeOf)
    (output : Stored.Lower.Output) : MapEntryComparison grow sig :=
  if key = .string then LiveStringMapEntryThen profile ready base bindings older destination inst element output
  else LiveMapEntryThen profile ready base bindings destination inst
    (Stored.Endpoints.RecordLower.CanonicalTree.EntryMode.forOutput destination.width (.map key element) output)

abbrev MapEntryTrail (grow : SingleThreaded.GrowOracle) (sig : Signature) :=
  Stored.Endpoints.RecordLower.Field → Stored.Endpoints.RecordLower.Field → Nat → Nat →
    LinkedCallback.MemorySequence.CheckNext grow sig → LinkedCallback.MemorySequence.CanonNext grow sig →
    TrailFinish grow sig → TrailFinish grow sig

/-- The string-key plan, real descriptor stores, and live value placement.
The value visitor is entered only at the reached continuation. -/
def stringMapEntryOccurrencePaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (element : Stored.TypeOf) (output : Stored.Lower.Output) (start incoming : Config (core3 grow) (HostState sig))
    (child : TrailFieldComparison grow sig) : MapEntryTrail grow sig :=
  open Stored.Endpoints.RecordLower ABI LinkedCallback.MemorySequence in
  fun field value index slot checkNext canonNext finish before left right check canon =>
    ∃ key : LinkedCallback.StringField, field = key.field ∧
      let cx := destination.context inst
      let mode := CanonicalTree.EntryMode.forOutput destination.width (.map .string element) output
      let keyArea := layout destination.width key.field.type
      let address := alignTo slot keyArea.alignment
      let afterKey := address + keyArea.size
      let valuePtr := alignTo afterKey (layout destination.width value.type).alignment
      let report := aggregateNext index checkNext
      let checked := fun verdict : Except Stored.Endpoints.RecordLower.Issue Unit => (match verdict with
        | .error issue => pure (.error issue)
        | .ok () => Record.Effects.field recordClaims Limits.spec Quirks.none cx destination.width value 1 (.memory valuePtr)) >>= report
      let canonical := fun () => mapValueProgram destination inst mode value afterKey canonNext
      StringValueOccurrencePaths profile ready base bindings older destination inst key (.memory address)
        start incoming left right check canon checked canonical (fun _ observed _ _ _ _ =>
          LocalOccurrenceThen profile ready base bindings start incoming observed
            (child value 1 valuePtr report canonNext finish)) before

def mapEntryOccurrencePaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (key : WIT.KeyType) (element : Stored.TypeOf) (output : Stored.Lower.Output)
    (start incoming : Config (core3 grow) (HostState sig)) (child : TrailFieldComparison grow sig) : MapEntryTrail grow sig :=
  if key = .string then
    stringMapEntryOccurrencePaths profile ready base bindings older destination inst element output start incoming child
  else
    open ABI LinkedCallback.MemorySequence in
    fun field value index slot checkNext canonNext finish before _ _ _ _ =>
      let keyArea := layout destination.width field.type
      let valuePtr := alignTo (alignTo slot keyArea.alignment + keyArea.size) (layout destination.width value.type).alignment
      LocalOccurrenceThen profile ready base bindings start incoming before
        (child value 1 valuePtr (aggregateNext index checkNext) canonNext finish)

/-- A reached string key transports all enclosing marks through its plan,
descriptor and placement. The value continuation is available only after
the descriptor and canonical placement have executed. -/
def StringMapEntryTransport (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (element : Stored.TypeOf) (output : Stored.Lower.Output) (start incoming : Config (core3 grow) (HostState sig))
    (visit : Nat → TrailFinish grow sig) (field value : Stored.Endpoints.RecordLower.Field) (index slot : Nat)
    (checkNext : LinkedCallback.MemorySequence.CheckNext grow sig) (canonNext : LinkedCallback.MemorySequence.CanonNext grow sig) :
    TrailFinish grow sig :=
  open Stored.Endpoints.RecordLower ABI LinkedCallback.MemorySequence in
  fun before left right check canon =>
    ∃ key : LinkedCallback.StringField, field = key.field ∧
      let cx := destination.context inst
      let mode := CanonicalTree.EntryMode.forOutput destination.width (.map .string element) output
      let keyArea := layout destination.width key.field.type
      let address := alignTo slot keyArea.alignment
      let afterKey := address + keyArea.size
      let valuePtr := alignTo afterKey (layout destination.width value.type).alignment
      let report := aggregateNext index checkNext
      let checked := fun verdict : Except Stored.Endpoints.RecordLower.Issue Unit => (match verdict with
        | .error issue => pure (.error issue)
        | .ok () => Record.Effects.field recordClaims Limits.spec Quirks.none cx destination.width value 1 (.memory valuePtr)) >>= report
      let canonical := fun () => mapValueProgram destination inst mode value afterKey canonNext
      StringValueOccurrencePaths profile ready base bindings older destination inst key (.memory address)
        start incoming left right check canon checked canonical (fun _ _ _ _ cursor peer =>
          (∃ prior reason lhs rhs, ComparedOccurrenceTransport profile ready base bindings start incoming (prior ++ [.trap reason]) lhs rhs ∧
            lhs.ctl = [] ∧ rhs.ctl = []) ∨
          (∃ observed lhs rhs, ComparedOccurrenceTransport profile ready base bindings start incoming observed lhs rhs ∧
            visit valuePtr observed lhs rhs cursor peer)) before start incoming

def stringMapEntryTransportPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (element : Stored.TypeOf) (output : Stored.Lower.Output) (start incoming : Config (core3 grow) (HostState sig))
    (child : TrailFieldComparison grow sig) : MapEntryTrail grow sig :=
  fun field value index slot checkNext canonNext finish =>
    StringMapEntryTransport profile ready base bindings older destination inst element output start incoming
      (fun pointer => child value 1 pointer (LinkedCallback.MemorySequence.aggregateNext index checkNext) canonNext finish)
      field value index slot checkNext canonNext

/-- Select the reached key program before the recursive value. The
canonical entry mode is fixed by the allocation's output, not the value. -/
def mapEntryTransportPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (key : WIT.KeyType) (element : Stored.TypeOf) (output : Stored.Lower.Output)
    (start incoming : Config (core3 grow) (HostState sig)) (child : TrailFieldComparison grow sig) : MapEntryTrail grow sig :=
  if key = .string then
    stringMapEntryTransportPaths profile ready base bindings older destination inst element output start incoming child
  else
    open ABI LinkedCallback.MemorySequence in
    fun field value index slot checkNext canonNext finish before _ _ _ _ =>
      let keyArea := layout destination.width field.type
      let valuePtr := alignTo (alignTo slot keyArea.alignment + keyArea.size) (layout destination.width value.type).alignment
      LocalTransportThen profile ready base bindings start incoming before
        (child value 1 valuePtr (aggregateNext index checkNext) canonNext finish)

def liveMapEntryPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (key : WIT.KeyType) (element : Stored.TypeOf) (output : Stored.Lower.Output)
    (start incoming : Config (core3 grow) (HostState sig)) (offset : Nat) (child : TrailFieldComparison grow sig) : MapEntryTrail grow sig :=
  open ABI LinkedCallback.MemorySequence in
  fun field value index slot checkNext canonNext finish before left right check canon =>
    let after := fun addr => child value 1 addr (aggregateNext index checkNext) canonNext finish
    if key = .string then
      LiveStringMapEntryPaths profile ready base bindings older destination inst element output start incoming before offset
        field value index slot checkNext canonNext after left right check canon
    else
      let keyArea := layout destination.width field.type
      let valuePtr := alignTo (alignTo slot keyArea.alignment + keyArea.size) (layout destination.width value.type).alignment
      LocalPathsThen profile ready base bindings start incoming before offset (after valuePtr)

def liveMapElementsPaths (entry : MapEntryTrail grow sig)
    (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType) (element : Stored.TypeOf)
    (output : Stored.Lower.Output) (checkNext : LinkedCallback.MemorySequence.CheckNext grow sig)
    (canonNext : LinkedCallback.MemorySequence.CanonNext grow sig) (finish : TrailFinish grow sig) :
    List Stored.Endpoints.RecordLower.Field → Nat → Nat → TrailFinish grow sig
  | [], _, _, before, left, right, check, canon => finish before left right check canon
  | item :: rest, index, pointer, before, left, right, check, canon =>
    open Stored.Endpoints.RecordLower ABI LinkedCallback.MemorySequence in
    let entryType : Stored.TypeOf := .record (mapEntryFields key element)
    let stride := (layout destination.width entryType).size
    let mode := CanonicalTree.EntryMode.forOutput destination.width (.map key element) output
    ∃ (payload : Stored.Payload (.prim key.toPrimitive)) (value : Field),
      let keyField := Field.data (.prim key.toPrimitive) payload
      item = .aggregate entryType [keyField, value] ∧
      entry keyField value index pointer
        (checkTail (.elements stride) destination inst rest (index + 1) (pointer + stride) checkNext)
        (fun () => CanonicalTree.elements Limits.spec Quirks.none (destination.context inst) destination.width
          rest mode stride (pointer + stride) >>= canonNext)
        (liveMapElementsPaths entry destination inst key element output checkNext canonNext finish
          rest (index + 1) (pointer + stride)) before left right check canon

def liveMapTailPaths (entry : MapEntryTrail grow sig)
    (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType) (element : Stored.TypeOf)
    (entries : List Stored.Endpoints.RecordLower.Field) (index : Nat) (output : Stored.Lower.Output)
    (checkNext : LinkedCallback.MemorySequence.ValueCheckNext grow sig output)
    (canonNext : LinkedCallback.MemorySequence.ValueCanonNext grow sig output)
    (publish : TrailFinish grow sig) : Nat → Nat → TrailFinish grow sig :=
  open LinkedCallback.MemorySequence in
  fun pointer _ => liveMapElementsPaths entry destination inst key element output
    (publishChecked destination inst pointer entries.length index output checkNext)
    (publishCanonical destination inst pointer entries.length output canonNext) publish entries 0 pointer

def liveFixedPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (destination : RecordDestination) (inst : InstId) (child : TrailFieldComparison grow sig)
    (element : Stored.TypeOf) (entries : List Stored.Endpoints.RecordLower.Field) (index address : Nat)
    (checkNext : LinkedCallback.MemorySequence.CheckNext grow sig) (canonNext : LinkedCallback.MemorySequence.CanonNext grow sig)
    (finish : TrailFinish grow sig) : TrailFinish grow sig :=
  open ABI LinkedCallback.MemorySequence ReturnFrame.Occurrence in
  fun before left right check canon =>
    let stride := (layout destination.width element).size
    let reference := { right with ctl := canon.control (Track.canonical (.elements stride) destination inst entries address >>= canonNext) }
    (∀ place, Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base)) right place [.tau] reference place) ∧
    liveElementsPaths destination inst stride child (aggregateNext index checkNext) canonNext finish entries 0 address
      before left reference check canon

/-- Both dispatchers run the actual local operations. Traps keep the stores
at the reached fault; only a successful field enters the continuation. -/
def LiveLocalFieldThen (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (checkNext : LinkedCallback.MemorySequence.CheckNext grow sig) (canonNext : LinkedCallback.MemorySequence.CanonNext grow sig)
    (finish : LinkedCallback.MemorySequence.Finish grow sig) (left right : Config (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) : Prop :=
  let checked := specDispatch ready base
  let canonical := specDispatch ready (LiveDispatch.host bindings base)
  ∃ (store : CStore (core3 grow)) (result : Except TrapReason Unit) (lhsLabels rhsLabels : Trace grow sig),
    let lhs := localLeafEnd left left.host store check.thread check.frames check.rest (fun res => checkNext (.ok res)) result
    let rhs := localLeafEnd right right.host store canon.thread canon.frames canon.rest canonNext result
    Steps profile ready checked left lhsLabels lhs ∧ Steps profile ready canonical right rhsLabels rhs ∧
    PayloadPrefix.visible lhsLabels = PayloadPrefix.visible rhsLabels ∧
    OccurrenceTransport profile ready base bindings left right lhsLabels rhsLabels lhs rhs ∧
    match result with
    | .error reason => ∃ leading, PayloadPrefix.visible rhsLabels = leading ++ [.trap reason]
    | .ok () => ReturnFrame.Occurrence.RetainsActiveSlots profile ready checked left lhsLabels lhs ∧
      ReturnFrame.Occurrence.RetainsActiveSlots profile ready canonical right rhsLabels rhs ∧ finish lhs rhs check canon

/-- Write the reached discriminant before visiting the selected payload.
A trapped tag write never enters the child continuation. -/
def LiveSumThen (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (destination : RecordDestination) (inst : InstId) (child : LinkedCallback.MemorySequence.FieldComparison grow sig)
    (arms : List (Option Stored.TypeOf)) (selected : Option Stored.Endpoints.RecordLower.Field) (index address : Nat)
    (checkNext : LinkedCallback.MemorySequence.CheckNext grow sig) (canonNext : LinkedCallback.MemorySequence.CanonNext grow sig)
    (finish : LinkedCallback.MemorySequence.Finish grow sig) (left right : Config (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) : Prop :=
  open PayloadPrefix LinkedCallback.MemorySequence ReturnFrame.Occurrence in
  let addr := sumPayloadAddress destination.width arms address
  let checked := specDispatch ready base
  let canonical := specDispatch ready (LiveDispatch.host bindings base)
  let lhsNext := sumCheckedNext destination inst selected index addr checkNext
  let rhsNext := sumCanonicalNext destination inst selected addr canonNext
  ∃ (store : CStore (core3 grow)) (result : Except TrapReason Unit) (lhsLabels rhsLabels : Trace grow sig),
    let lhs := localLeafEnd left left.host store check.thread check.frames check.rest lhsNext result
    let rhs := localLeafEnd right right.host store canon.thread canon.frames canon.rest rhsNext result
    Steps profile ready checked left lhsLabels lhs ∧ Steps profile ready canonical right rhsLabels rhs ∧
    visible lhsLabels = visible rhsLabels ∧
    OccurrenceTransport profile ready base bindings left right lhsLabels rhsLabels lhs rhs ∧
    match result with
    | .error reason => ∃ leading, visible rhsLabels = leading ++ [.trap reason]
    | .ok () => RetainsActiveSlots profile ready checked left lhsLabels lhs ∧
      RetainsActiveSlots profile ready canonical right rhsLabels rhs ∧
      match selected with
      | none => finish lhs rhs check canon
      | some item => child item 0 addr lhs rhs check canon (aggregateNext index checkNext) canonNext finish

def LiveFixedThen (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (destination : RecordDestination) (inst : InstId) (child : LinkedCallback.MemorySequence.FieldComparison grow sig)
    (element : Stored.TypeOf) (entries : List Stored.Endpoints.RecordLower.Field) (index address : Nat)
    (checkNext : LinkedCallback.MemorySequence.CheckNext grow sig) (canonNext : LinkedCallback.MemorySequence.CanonNext grow sig)
    (finish : LinkedCallback.MemorySequence.Finish grow sig) (left right : Config (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) : Prop :=
  open ABI Stored.Endpoints.RecordLower LinkedCallback.MemorySequence ReturnFrame.Occurrence in
  let stride := (layout destination.width element).size
  let reference := { right with ctl := canon.control (Track.canonical (.elements stride) destination inst entries address >>= canonNext) }
  (∀ place, Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base)) right place [.tau] reference place) ∧
    liveElements destination inst stride child (aggregateNext index checkNext) canonNext finish entries 0 address left reference check canon

def LiveAggregateThen (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (destination : RecordDestination) (inst : InstId) (child : LinkedCallback.MemorySequence.FieldComparison grow sig)
    (items : List Stored.Endpoints.RecordLower.Field) (index address : Nat)
    (checkNext : LinkedCallback.MemorySequence.CheckNext grow sig) (canonNext : LinkedCallback.MemorySequence.CanonNext grow sig)
    (finish : LinkedCallback.MemorySequence.Finish grow sig) (left right : Config (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) : Prop :=
  open LinkedCallback.MemorySequence ReturnFrame.Occurrence in
  let entered := enterAggregate destination inst items index address left check checkNext
  (∀ place, Prefix profile ready (specDispatch ready base) left place [.tau] entered place) ∧
    ReplayBetween profile ready (specDispatch ready (LiveDispatch.host bindings base)) .fields destination inst child
      (aggregateNext index checkNext) canonNext finish items 0 address entered right check canon

def aggregateChild (comparisons : List (Stored.TypeOf × LinkedCallback.MemorySequence.FieldComparison grow sig)) :
    LinkedCallback.MemorySequence.FieldComparison grow sig :=
  fun item index address left right check canon checkNext canonNext finish =>
    ∃ compare, (item.type, compare) ∈ comparisons ∧ compare item index address left right check canon checkNext canonNext finish

/-- The actual aggregate bounds read precedes the field-by-field replay. -/
def liveAggregatePaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (destination : RecordDestination) (inst : InstId) (child : TrailFieldComparison grow sig)
    (items : List Stored.Endpoints.RecordLower.Field) (index address : Nat)
    (checkNext : LinkedCallback.MemorySequence.CheckNext grow sig) (canonNext : LinkedCallback.MemorySequence.CanonNext grow sig)
    (finish : TrailFinish grow sig) : TrailFinish grow sig :=
  open LinkedCallback.MemorySequence ReturnFrame.Occurrence in
  fun before left right check canon =>
    let entered := enterAggregate destination inst items index address left check checkNext
    ComparedOccurrencePaths profile ready base bindings left right [] entered right ∧
      replayBetweenPaths profile ready base bindings .fields destination inst child
        (aggregateNext index checkNext) canonNext finish items 0 address before entered right check canon

def selectFieldPaths (paths : Stored.TypeOf → TrailFieldComparison grow sig) : TrailFieldComparison grow sig :=
  fun item => paths item.type item

/-- Leaf-only aggregates are one instance of the common sibling fold. -/
inductive TrailLeafAggregate : Stored.TypeOf → Prop where
  | record {fields} : (∀ field ∈ fields, TrailLeafType field.2) → TrailLeafAggregate (.record fields)
  | tuple {types} : (∀ type ∈ types, TrailLeafType type) → TrailLeafAggregate (.tuple types)

def aggregateFieldPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (destination : RecordDestination) (inst : InstId) (type : Stored.TypeOf)
    (paths : Stored.TypeOf → TrailFieldComparison grow sig) : TrailFieldComparison grow sig :=
  fun item index address checkNext canonNext finish before left right check canon =>
    ∃ items, item = .aggregate type items ∧
      liveAggregatePaths profile ready base bindings destination inst (selectFieldPaths paths) items index address
        checkNext canonNext finish before left right check canon

mutual
/-- Recursion follows the declared type, not the number of reached allocator
returns. Each map selects the actual key rule before visiting its value. -/
def liveCollectionField (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId) :
    Stored.TypeOf → LinkedCallback.MemorySequence.FieldComparison grow sig
  | .list element => fun item index address left right check canon checkNext canonNext finish =>
    ∃ entries, item = .dynamic (.list element) element entries ∧
      LiveCollectionEntry profile ready base bindings older destination inst (.list element) element entries index
        (.memory address) checkNext canonNext left right check canon
        (fun pointer bytes _ => liveListTail profile ready base bindings destination inst element entries index (.memory address)
          (liveCollectionField profile ready base bindings older destination inst element) checkNext canonNext (fun () => finish) pointer bytes)
  | .map key element => fun item index address left right check canon checkNext canonNext finish =>
    let entryType : Stored.TypeOf := .record (ABI.mapEntryFields key element)
    let output := Stored.Lower.Output.memory address
    ∃ entries, item = .dynamic (.map key element) entryType entries ∧
      LiveCollectionEntry profile ready base bindings older destination inst (.map key element) entryType entries index
        output checkNext canonNext left right check canon
        (fun pointer bytes _ => liveMapTailWith profile ready base bindings (liveCollectionMapEntry profile ready base bindings older destination inst key element output)
          destination inst key element entries index output
          (liveCollectionField profile ready base bindings older destination inst element) checkNext canonNext (fun () => finish) pointer bytes)
  | .fixedList element length => fun item index address left right check canon checkNext canonNext finish =>
    ∃ entries, item = .fixed element length entries ∧
      LiveFixedThen profile ready base bindings destination inst (liveCollectionField profile ready base bindings older destination inst element)
        element entries index address checkNext canonNext finish left right check canon
  | .option element => fun item index address left right check canon checkNext canonNext finish =>
    ∃ tag selected, item = .sum (.option element) [none, some element] tag selected ∧
      LiveSumThen profile ready base bindings destination inst (liveCollectionField profile ready base bindings older destination inst element)
        [none, some element] selected index address checkNext canonNext finish left right check canon
  | .result success failure => fun item index address left right check canon checkNext canonNext finish =>
    ∃ tag selected, item = .sum (.result success failure) [success, failure] tag selected ∧
      let okCompare : LinkedCallback.MemorySequence.FieldComparison grow sig := match success with
        | some type => liveCollectionField profile ready base bindings older destination inst type
        | none => fun _ _ _ _ _ _ _ _ _ _ => False
      let errCompare : LinkedCallback.MemorySequence.FieldComparison grow sig := match failure with
        | some type => liveCollectionField profile ready base bindings older destination inst type
        | none => fun _ _ _ _ _ _ _ _ _ _ => False
      LiveSumThen profile ready base bindings destination inst (if tag = 0 then okCompare else errCompare)
        [success, failure] selected index address checkNext canonNext finish left right check canon
  | .variant cases => fun item index address left right check canon checkNext canonNext finish =>
    ∃ tag selected, item = .sum (.variant cases) (cases.map Prod.snd) tag selected ∧
      LiveSumThen profile ready base bindings destination inst
        (liveVariantArm profile ready base bindings older destination inst cases tag)
        (cases.map Prod.snd) selected index address checkNext canonNext finish left right check canon
  | .record fields => fun item index address left right check canon checkNext canonNext finish =>
    ∃ items, item = .aggregate (.record fields) items ∧
      LiveAggregateThen profile ready base bindings destination inst
        (aggregateChild (liveRecordFields profile ready base bindings older destination inst fields))
        items index address checkNext canonNext finish left right check canon
  | .tuple types => fun item index address left right check canon checkNext canonNext finish =>
    ∃ items, item = .aggregate (.tuple types) items ∧
      LiveAggregateThen profile ready base bindings destination inst
        (aggregateChild (liveTupleFields profile ready base bindings older destination inst types))
        items index address checkNext canonNext finish left right check canon
  | .prim .string => fun item _ address left right check canon checkNext canonNext finish =>
    ∃ str : LinkedCallback.StringField, item = str.field ∧
      StringKeyThen profile ready base bindings older destination inst str address left right check canon checkNext canonNext
        (fun _ => LiveLocalFieldThen profile ready base bindings checkNext canonNext finish)
  | .prim _ | .enum _ | .flags _ => fun _ _ _ left right check canon checkNext canonNext finish =>
    LiveLocalFieldThen profile ready base bindings checkNext canonNext finish left right check canon
  | _ => fun item index address left right check canon checkNext canonNext finish =>
    LinkedCallback.HandleFieldThenBetween profile ready (specDispatch ready base)
      (specDispatch ready (LiveDispatch.host bindings base)) item index (.memory address) left right check canon
      checkNext canonNext (fun () => finish)
termination_by structural type => type

def liveVariantArm (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId) :
    List (String × Option Stored.TypeOf) → Nat → LinkedCallback.MemorySequence.FieldComparison grow sig
  | (_, some type) :: _, 0 => liveCollectionField profile ready base bindings older destination inst type
  | _ :: rest, tag + 1 => liveVariantArm profile ready base bindings older destination inst rest tag
  | _, _ => fun _ _ _ _ _ _ _ _ _ _ => False
termination_by structural cases => cases

def liveRecordFields (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId) :
    List (String × Stored.TypeOf) → List (Stored.TypeOf × LinkedCallback.MemorySequence.FieldComparison grow sig)
  | [] => []
  | (_, type) :: rest => (type, liveCollectionField profile ready base bindings older destination inst type) ::
      liveRecordFields profile ready base bindings older destination inst rest
termination_by structural fields => fields

def liveTupleFields (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId) :
    List Stored.TypeOf → List (Stored.TypeOf × LinkedCallback.MemorySequence.FieldComparison grow sig)
  | [] => []
  | type :: rest => (type, liveCollectionField profile ready base bindings older destination inst type) ::
      liveTupleFields profile ready base bindings older destination inst rest
termination_by structural fields => fields
end

def selectPathField (paths : List (Stored.TypeOf × TrailFieldComparison grow sig)) : TrailFieldComparison grow sig :=
  fun item index address checkNext canonNext finish before left right check canon =>
    ∃ compare, (item.type, compare) ∈ paths ∧ compare item index address checkNext canonNext finish before left right check canon

mutual
/-- Thread one occurrence origin through the actual compiled shape. At a
dynamic child preserve its marked allocator cut; only entered descendants
may proceed to their descriptor and the next sibling. -/
def liveRecursivePaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (offset : Nat) (sink : RefusalSink grow sig) :
    Stored.TypeOf → TrailFieldComparison grow sig
  | .list element => fun item index address checkNext canonNext finish before left right check canon =>
    ∃ entries, item = .dynamic (.list element) element entries ∧
      LiveCollectionEntry profile ready base bindings older destination inst (.list element) element entries index
        (.memory address) checkNext canonNext left right check canon
        (liveListTailPaths destination inst element entries index (.memory address)
          (liveRecursivePaths profile ready base bindings older destination inst start incoming offset sink element)
          checkNext canonNext (fun observed _ _ _ _ => LocalPathsThen profile ready base bindings start incoming observed offset finish))
        start incoming before offset sink
  | .map key element => fun item index address checkNext canonNext finish before left right check canon =>
    let entryType : Stored.TypeOf := .record (ABI.mapEntryFields key element)
    let output := Stored.Lower.Output.memory address
    ∃ entries, item = .dynamic (.map key element) entryType entries ∧
      LiveCollectionEntry profile ready base bindings older destination inst (.map key element) entryType entries index
        output checkNext canonNext left right check canon
        (liveMapTailPaths (liveMapEntryPaths profile ready base bindings older destination inst key element output start incoming offset
          (liveRecursivePaths profile ready base bindings older destination inst start incoming offset sink element))
          destination inst key element entries index output checkNext canonNext
          (fun observed _ _ _ _ => LocalPathsThen profile ready base bindings start incoming observed offset finish))
        start incoming before offset sink
  | .fixedList element length => fun item index address checkNext canonNext finish before left right check canon =>
    ∃ entries, item = .fixed element length entries ∧
      liveFixedPaths profile ready base bindings destination inst
        (liveRecursivePaths profile ready base bindings older destination inst start incoming offset sink element) element entries index address
        checkNext canonNext finish before left right check canon
  | .option element => fun item index address checkNext canonNext finish before left right _ _ =>
    ∃ tag selected, item = .sum (.option element) [none, some element] tag selected ∧
      LocatedLocalPathsThen profile ready base bindings start incoming left right before offset
        (match selected with
        | none => finish
        | some arm => liveRecursivePaths profile ready base bindings older destination inst start incoming offset sink element arm 0
            (PayloadPrefix.sumPayloadAddress destination.width [none, some element] address)
            (LinkedCallback.MemorySequence.aggregateNext index checkNext) canonNext finish)
  | .result success failure => fun item index address checkNext canonNext finish before left right _ _ =>
    ∃ tag selected, item = .sum (.result success failure) [success, failure] tag selected ∧
      let okPaths : TrailFieldComparison grow sig := match success with
        | some type => liveRecursivePaths profile ready base bindings older destination inst start incoming offset sink type
        | none => fun _ _ _ _ _ _ _ _ _ _ _ => False
      let errorPaths : TrailFieldComparison grow sig := match failure with
        | some type => liveRecursivePaths profile ready base bindings older destination inst start incoming offset sink type
        | none => fun _ _ _ _ _ _ _ _ _ _ _ => False
      LocatedLocalPathsThen profile ready base bindings start incoming left right before offset
        (match selected with
        | none => finish
        | some arm => (if tag = 0 then okPaths else errorPaths) arm 0 (PayloadPrefix.sumPayloadAddress destination.width [success, failure] address)
            (LinkedCallback.MemorySequence.aggregateNext index checkNext) canonNext finish)
  | .variant cases => fun item index address checkNext canonNext finish before left right _ _ =>
    ∃ tag selected, item = .sum (.variant cases) (cases.map Prod.snd) tag selected ∧
      LocatedLocalPathsThen profile ready base bindings start incoming left right before offset
        (match selected with
        | none => finish
        | some arm => liveVariantPaths profile ready base bindings older destination inst start incoming offset sink cases tag arm 0
            (PayloadPrefix.sumPayloadAddress destination.width (cases.map Prod.snd) address)
            (LinkedCallback.MemorySequence.aggregateNext index checkNext) canonNext finish)
  | .record fields => fun item index address checkNext canonNext finish before left right check canon =>
    ∃ items, item = .aggregate (.record fields) items ∧
      liveAggregatePaths profile ready base bindings destination inst
        (selectPathField (liveRecordTrails profile ready base bindings older destination inst start incoming offset sink fields))
        items index address checkNext canonNext finish before left right check canon
  | .tuple types => fun item index address checkNext canonNext finish before left right check canon =>
    ∃ items, item = .aggregate (.tuple types) items ∧
      liveAggregatePaths profile ready base bindings destination inst
        (selectPathField (liveTupleTrails profile ready base bindings older destination inst start incoming offset sink types))
        items index address checkNext canonNext finish before left right check canon
  | type => liveLeafPaths profile ready base bindings older destination inst start incoming offset sink type
termination_by structural type => type

def liveVariantPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (offset : Nat) (sink : RefusalSink grow sig) :
    List (String × Option Stored.TypeOf) → Nat → TrailFieldComparison grow sig
  | (_, some type) :: _, 0 => liveRecursivePaths profile ready base bindings older destination inst start incoming offset sink type
  | _ :: rest, tag + 1 => liveVariantPaths profile ready base bindings older destination inst start incoming offset sink rest tag
  | _, _ => fun _ _ _ _ _ _ _ _ _ _ _ => False
termination_by structural cases => cases

def liveRecordTrails (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (offset : Nat) (sink : RefusalSink grow sig) :
    List (String × Stored.TypeOf) → List (Stored.TypeOf × TrailFieldComparison grow sig)
  | [] => []
  | (_, type) :: rest => (type, liveRecursivePaths profile ready base bindings older destination inst start incoming offset sink type) ::
      liveRecordTrails profile ready base bindings older destination inst start incoming offset sink rest
termination_by structural fields => fields

def liveTupleTrails (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (offset : Nat) (sink : RefusalSink grow sig) :
    List Stored.TypeOf → List (Stored.TypeOf × TrailFieldComparison grow sig)
  | [] => []
  | type :: rest => (type, liveRecursivePaths profile ready base bindings older destination inst start incoming offset sink type) ::
      liveTupleTrails profile ready base bindings older destination inst start incoming offset sink rest
termination_by structural types => types
end

/-- The enclosing-mark invariant covers the compiled memory visitor's
recursive fragment; it is not a runtime admission predicate. -/
abbrev RecursiveAllocatingTransportType := RecursiveCollectionType

mutual
/-- Follow each reached child of the compiled memory visitor, carrying the
enclosing marks through the real placement, allocator and continuation. -/
def recursiveAllocatingTransportPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (sink : RefusalSink grow sig) : Stored.TypeOf → TrailFieldComparison grow sig
  | .list element => fun item index address checkNext canonNext finish before left right check canon =>
    ∃ entries, item = .dynamic (.list element) element entries ∧
      LiveCollectionOccurrenceEntry profile ready base bindings older destination inst (.list element) element entries index
        (.memory address) checkNext canonNext start incoming left right before check canon
        (liveListTailPaths destination inst element entries index (.memory address)
          (recursiveAllocatingTransportPaths profile ready base bindings older destination inst start incoming sink element) checkNext canonNext
          (fun observed _ _ _ _ => LocalTransportThen profile ready base bindings start incoming observed finish)) sink
  | .map key element => fun item index address checkNext canonNext finish before left right check canon =>
    let entryType : Stored.TypeOf := .record (ABI.mapEntryFields key element)
    let output := Stored.Lower.Output.memory address
    ∃ entries, item = .dynamic (.map key element) entryType entries ∧
      LiveCollectionOccurrenceEntry profile ready base bindings older destination inst (.map key element) entryType entries index
        output checkNext canonNext start incoming left right before check canon
        (liveMapTailPaths (mapEntryTransportPaths profile ready base bindings older destination inst key element output start incoming
          (recursiveAllocatingTransportPaths profile ready base bindings older destination inst start incoming sink element))
          destination inst key element entries index output checkNext canonNext
          (fun observed _ _ _ _ => LocalTransportThen profile ready base bindings start incoming observed finish)) sink
  | .fixedList element length => fun item index address checkNext canonNext finish before left right check canon =>
    ∃ entries, item = .fixed element length entries ∧
      liveFixedPaths profile ready base bindings destination inst
        (recursiveAllocatingTransportPaths profile ready base bindings older destination inst start incoming sink element)
        element entries index address checkNext canonNext finish before left right check canon
  | .option element => fun item index address checkNext canonNext finish before _ _ _ _ =>
    ∃ tag selected, item = .sum (.option element) [none, some element] tag selected ∧
      LocalTransportThen profile ready base bindings start incoming before
        (match selected with
        | none => finish
        | some arm => recursiveAllocatingTransportPaths profile ready base bindings older destination inst start incoming sink element arm 0
            (PayloadPrefix.sumPayloadAddress destination.width [none, some element] address)
            (LinkedCallback.MemorySequence.aggregateNext index checkNext) canonNext finish)
  | .result success failure => fun item index address checkNext canonNext finish before _ _ _ _ =>
    ∃ tag selected, item = .sum (.result success failure) [success, failure] tag selected ∧
      let okPaths : TrailFieldComparison grow sig := match success with
        | some type => recursiveAllocatingTransportPaths profile ready base bindings older destination inst start incoming sink type
        | none => fun _ _ _ _ _ _ _ _ _ _ _ => False
      let errorPaths : TrailFieldComparison grow sig := match failure with
        | some type => recursiveAllocatingTransportPaths profile ready base bindings older destination inst start incoming sink type
        | none => fun _ _ _ _ _ _ _ _ _ _ _ => False
      LocalTransportThen profile ready base bindings start incoming before
        (match selected with
        | none => finish
        | some arm => (if tag = 0 then okPaths else errorPaths) arm 0
            (PayloadPrefix.sumPayloadAddress destination.width [success, failure] address)
            (LinkedCallback.MemorySequence.aggregateNext index checkNext) canonNext finish)
  | .variant cases => fun item index address checkNext canonNext finish before _ _ _ _ =>
    ∃ tag selected, item = .sum (.variant cases) (cases.map Prod.snd) tag selected ∧
      LocalTransportThen profile ready base bindings start incoming before
        (match selected with
        | none => finish
        | some arm => recursiveVariantTransportPaths profile ready base bindings older destination inst start incoming sink cases tag arm 0
            (PayloadPrefix.sumPayloadAddress destination.width (cases.map Prod.snd) address)
            (LinkedCallback.MemorySequence.aggregateNext index checkNext) canonNext finish)
  | .record fields => fun item index address checkNext canonNext finish before left right check canon =>
    ∃ items, item = .aggregate (.record fields) items ∧
      liveAggregatePaths profile ready base bindings destination inst
        (selectPathField (recursiveRecordTransportPaths profile ready base bindings older destination inst start incoming sink fields))
        items index address checkNext canonNext finish before left right check canon
  | .tuple types => fun item index address checkNext canonNext finish before left right check canon =>
    ∃ items, item = .aggregate (.tuple types) items ∧
      liveAggregatePaths profile ready base bindings destination inst
        (selectPathField (recursiveTupleTransportPaths profile ready base bindings older destination inst start incoming sink types))
        items index address checkNext canonNext finish before left right check canon
  | .prim .string => fun item _ address checkNext canonNext finish seen left right check canon =>
    ∃ str : LinkedCallback.StringField, item = str.field ∧
      StringValueOccurrencePaths profile ready base bindings older destination inst str (.memory address)
        start incoming left right check canon checkNext canonNext
        (fun _ _ _ _ _ _ => ∃ seen, LocalTransportThen profile ready base bindings start incoming seen finish) seen start incoming
  | .prim _ | .enum _ | .flags _ => fun _ _ _ _ _ finish seen _ _ _ _ =>
    LocalTransportThen profile ready base bindings start incoming seen finish
  | _ => fun item index _ checkNext _ finish seen left right check _ =>
    HandleTransportThen profile ready base bindings start incoming left right seen item index check checkNext finish sink
termination_by structural type => type

def recursiveVariantTransportPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (sink : RefusalSink grow sig) :
    List (String × Option Stored.TypeOf) → Nat → TrailFieldComparison grow sig
  | (_, some type) :: _, 0 => recursiveAllocatingTransportPaths profile ready base bindings older destination inst start incoming sink type
  | _ :: rest, tag + 1 => recursiveVariantTransportPaths profile ready base bindings older destination inst start incoming sink rest tag
  | _, _ => fun _ _ _ _ _ _ _ _ _ _ _ => False
termination_by structural cases => cases

def recursiveRecordTransportPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (sink : RefusalSink grow sig) :
    List (String × Stored.TypeOf) → List (Stored.TypeOf × TrailFieldComparison grow sig)
  | [] => []
  | (_, type) :: rest => (type, recursiveAllocatingTransportPaths profile ready base bindings older destination inst start incoming sink type) ::
      recursiveRecordTransportPaths profile ready base bindings older destination inst start incoming sink rest
termination_by structural fields => fields

def recursiveTupleTransportPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (sink : RefusalSink grow sig) :
    List Stored.TypeOf → List (Stored.TypeOf × TrailFieldComparison grow sig)
  | [] => []
  | type :: rest => (type, recursiveAllocatingTransportPaths profile ready base bindings older destination inst start incoming sink type) ::
      recursiveTupleTransportPaths profile ready base bindings older destination inst start incoming sink rest
termination_by structural types => types
end

/-- The cumulative memory fold covers the same fragment as the compiled
recursive visitor, with no additional runtime admission condition. -/
abbrev StructuralMemoryOccurrenceType := RecursiveCollectionType

mutual
def structuralMemoryOccurrencePaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (sink : RefusalSink grow sig) :
    Stored.TypeOf → TrailFieldComparison grow sig
  | .list element => fun item index address checkNext canonNext finish before left right check canon =>
    ∃ entries, item = .dynamic (.list element) element entries ∧
      LiveCollectionOccurrenceEntry profile ready base bindings older destination inst (.list element) element entries index
        (.memory address) checkNext canonNext start incoming left right before check canon
        (liveListTailPaths destination inst element entries index (.memory address)
          (structuralMemoryOccurrencePaths profile ready base bindings older destination inst start incoming sink element)
          checkNext canonNext (fun observed _ _ _ _ => LocalOccurrenceThen profile ready base bindings start incoming observed finish)) sink
  | .map key element => fun item index address checkNext canonNext finish before left right check canon =>
    let entryType : Stored.TypeOf := .record (ABI.mapEntryFields key element)
    let output := Stored.Lower.Output.memory address
    ∃ entries, item = .dynamic (.map key element) entryType entries ∧
      LiveCollectionOccurrenceEntry profile ready base bindings older destination inst (.map key element) entryType entries index
        output checkNext canonNext start incoming left right before check canon
        (liveMapTailPaths (mapEntryOccurrencePaths profile ready base bindings older destination inst key element output start incoming
          (structuralMemoryOccurrencePaths profile ready base bindings older destination inst start incoming sink element))
          destination inst key element entries index output checkNext canonNext
          (fun observed _ _ _ _ => LocalOccurrenceThen profile ready base bindings start incoming observed finish)) sink
  | .fixedList element length => fun item index address checkNext canonNext finish before left right check canon =>
    ∃ entries, item = .fixed element length entries ∧
      liveFixedPaths profile ready base bindings destination inst
        (structuralMemoryOccurrencePaths profile ready base bindings older destination inst start incoming sink element) element entries index address
        checkNext canonNext finish before left right check canon
  | .option element => fun item index address checkNext canonNext finish before _ _ _ _ =>
    ∃ tag selected, item = .sum (.option element) [none, some element] tag selected ∧
      LocalOccurrenceThen profile ready base bindings start incoming before
        (match selected with
        | none => finish
        | some arm => structuralMemoryOccurrencePaths profile ready base bindings older destination inst start incoming sink element arm 0
            (PayloadPrefix.sumPayloadAddress destination.width [none, some element] address)
            (LinkedCallback.MemorySequence.aggregateNext index checkNext) canonNext finish)
  | .result success failure => fun item index address checkNext canonNext finish before _ _ _ _ =>
    ∃ tag selected, item = .sum (.result success failure) [success, failure] tag selected ∧
      let okPaths : TrailFieldComparison grow sig := match success with
        | some type => structuralMemoryOccurrencePaths profile ready base bindings older destination inst start incoming sink type
        | none => fun _ _ _ _ _ _ _ _ _ _ _ => False
      let errorPaths : TrailFieldComparison grow sig := match failure with
        | some type => structuralMemoryOccurrencePaths profile ready base bindings older destination inst start incoming sink type
        | none => fun _ _ _ _ _ _ _ _ _ _ _ => False
      LocalOccurrenceThen profile ready base bindings start incoming before
        (match selected with
        | none => finish
        | some arm => (if tag = 0 then okPaths else errorPaths) arm 0 (PayloadPrefix.sumPayloadAddress destination.width [success, failure] address)
            (LinkedCallback.MemorySequence.aggregateNext index checkNext) canonNext finish)
  | .variant cases => fun item index address checkNext canonNext finish before _ _ _ _ =>
    ∃ tag selected, item = .sum (.variant cases) (cases.map Prod.snd) tag selected ∧
      LocalOccurrenceThen profile ready base bindings start incoming before
        (match selected with
        | none => finish
        | some arm => structuralVariantOccurrencePaths profile ready base bindings older destination inst start incoming sink cases tag arm 0
            (PayloadPrefix.sumPayloadAddress destination.width (cases.map Prod.snd) address)
            (LinkedCallback.MemorySequence.aggregateNext index checkNext) canonNext finish)
  | .record fields => fun item index address checkNext canonNext finish before left right check canon =>
    ∃ items, item = .aggregate (.record fields) items ∧
      liveAggregatePaths profile ready base bindings destination inst
        (selectPathField (structuralRecordOccurrencePaths profile ready base bindings older destination inst start incoming sink fields))
        items index address checkNext canonNext finish before left right check canon
  | .tuple types => fun item index address checkNext canonNext finish before left right check canon =>
    ∃ items, item = .aggregate (.tuple types) items ∧
      liveAggregatePaths profile ready base bindings destination inst
        (selectPathField (structuralTupleOccurrencePaths profile ready base bindings older destination inst start incoming sink types))
        items index address checkNext canonNext finish before left right check canon
  | type => leafOccurrencePaths profile ready base bindings older destination inst start incoming sink type
termination_by structural type => type

def structuralVariantOccurrencePaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (sink : RefusalSink grow sig) :
    List (String × Option Stored.TypeOf) → Nat → TrailFieldComparison grow sig
  | (_, some type) :: _, 0 => structuralMemoryOccurrencePaths profile ready base bindings older destination inst start incoming sink type
  | _ :: rest, tag + 1 => structuralVariantOccurrencePaths profile ready base bindings older destination inst start incoming sink rest tag
  | _, _ => fun _ _ _ _ _ _ _ _ _ _ _ => False
termination_by structural cases => cases

def structuralRecordOccurrencePaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (sink : RefusalSink grow sig) :
    List (String × Stored.TypeOf) → List (Stored.TypeOf × TrailFieldComparison grow sig)
  | [] => []
  | (_, type) :: rest => (type, structuralMemoryOccurrencePaths profile ready base bindings older destination inst start incoming sink type) ::
      structuralRecordOccurrencePaths profile ready base bindings older destination inst start incoming sink rest
termination_by structural fields => fields

def structuralTupleOccurrencePaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (sink : RefusalSink grow sig) :
    List Stored.TypeOf → List (Stored.TypeOf × TrailFieldComparison grow sig)
  | [] => []
  | type :: rest => (type, structuralMemoryOccurrencePaths profile ready base bindings older destination inst start incoming sink type) ::
      structuralTupleOccurrencePaths profile ready base bindings older destination inst start incoming sink rest
termination_by structural types => types
end

mutual
def liveFlatPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (offset : Nat) (sink : RefusalSink grow sig) :
    Stored.TypeOf → FlatFieldTrail grow sig
  | .prim .string => fun item _ checkNext canonNext finish before left right check canon =>
    ∃ str : LinkedCallback.StringField, item = str.field ∧
      StringValuePaths profile ready base bindings older destination inst str .flat start incoming left right check canon checkNext canonNext
        (fun _ observed _ _ _ _ => LocalPathsThen profile ready base bindings start incoming observed offset (flatWordVisit finish))
        before offset
  | .list element => fun item index checkNext canonNext finish before left right check canon =>
    ∃ entries, item = .dynamic (.list element) element entries ∧
      LiveCollectionEntry profile ready base bindings older destination inst (.list element) element entries index
        .flat checkNext canonNext left right check canon
        (liveListTailPaths destination inst element entries index .flat
          (liveRecursivePaths profile ready base bindings older destination inst start incoming offset sink element)
          checkNext canonNext
          (fun seen _ _ _ _ => LocalPathsThen profile ready base bindings start incoming seen offset (flatWordVisit finish)))
        start incoming before offset sink
  | .map key element => fun item index checkNext canonNext finish before left right check canon =>
    let entryType : Stored.TypeOf := .record (ABI.mapEntryFields key element)
    ∃ entries, item = .dynamic (.map key element) entryType entries ∧
      LiveCollectionEntry profile ready base bindings older destination inst (.map key element) entryType entries index
        .flat checkNext canonNext left right check canon
        (liveMapTailPaths (liveMapEntryPaths profile ready base bindings older destination inst key element .flat start incoming offset
          (liveRecursivePaths profile ready base bindings older destination inst start incoming offset sink element))
          destination inst key element entries index .flat checkNext canonNext
          (fun seen _ _ _ _ => LocalPathsThen profile ready base bindings start incoming seen offset (flatWordVisit finish)))
        start incoming before offset sink
  | .fixedList element _ => flatAggregatePaths destination inst
      (liveFlatPaths profile ready base bindings older destination inst start incoming offset sink element)
  | .option element => flatSumPaths profile ready base bindings start incoming offset destination.width
      (.option element) [none, some element]
      (fun _ => liveFlatPaths profile ready base bindings older destination inst start incoming offset sink element)
  | .result success failure =>
    let first := match success with
      | none => noFlatChild
      | some type => liveFlatPaths profile ready base bindings older destination inst start incoming offset sink type
    let second := match failure with
      | none => noFlatChild
      | some type => liveFlatPaths profile ready base bindings older destination inst start incoming offset sink type
    flatSumPaths profile ready base bindings start incoming offset destination.width (.result success failure) [success, failure]
      (fun tag => if tag = 0 then first else second)
  | .variant cases => flatSumPaths profile ready base bindings start incoming offset destination.width
      (.variant cases) (cases.map Prod.snd) (liveFlatVariantPaths profile ready base bindings older destination inst start incoming offset sink cases)
  | .record fields => flatAggregatePaths destination inst
      (selectFlatPaths (liveFlatRecordPaths profile ready base bindings older destination inst start incoming offset sink fields))
  | .tuple types => flatAggregatePaths destination inst
      (selectFlatPaths (liveFlatTuplePaths profile ready base bindings older destination inst start incoming offset sink types))
  | .own _ | .future _ | .stream _ | .errorContext => fun item index checkNext _ finish before left right check _ =>
    HandlePathsThen profile ready base bindings start incoming before offset item index checkNext (flatWordVisit finish) left right check sink
  | _ => fun _ _ _ _ finish before left right _ _ =>
    LocatedLocalPathsThen profile ready base bindings start incoming left right before offset (flatWordVisit finish)
termination_by structural type => type

def liveFlatRecordPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (offset : Nat) (sink : RefusalSink grow sig) :
    List (String × Stored.TypeOf) → List (Stored.TypeOf × FlatFieldTrail grow sig)
  | [] => []
  | (_, type) :: rest =>
    (type, liveFlatPaths profile ready base bindings older destination inst start incoming offset sink type) ::
      liveFlatRecordPaths profile ready base bindings older destination inst start incoming offset sink rest
termination_by structural fields => fields

def liveFlatTuplePaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (offset : Nat) (sink : RefusalSink grow sig) :
    List Stored.TypeOf → List (Stored.TypeOf × FlatFieldTrail grow sig)
  | [] => []
  | type :: rest =>
    (type, liveFlatPaths profile ready base bindings older destination inst start incoming offset sink type) ::
      liveFlatTuplePaths profile ready base bindings older destination inst start incoming offset sink rest
termination_by structural types => types

def liveFlatVariantPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (offset : Nat) (sink : RefusalSink grow sig) :
    List (String × Option Stored.TypeOf) → Nat → FlatFieldTrail grow sig
  | [], _ | (_, none) :: _, 0 => noFlatChild
  | (_, some type) :: _, 0 => liveFlatPaths profile ready base bindings older destination inst start incoming offset sink type
  | _ :: rest, tag + 1 => liveFlatVariantPaths profile ready base bindings older destination inst start incoming offset sink rest tag
termination_by structural cases => cases
end

mutual
def structuralFlatOccurrencePaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (sink : RefusalSink grow sig) :
    Stored.TypeOf → FlatFieldTrail grow sig
  | .prim .string => fun item _ checkNext canonNext finish before left right check canon =>
    ∃ str : LinkedCallback.StringField, item = str.field ∧
      StringValueOccurrencePaths profile ready base bindings older destination inst str .flat start incoming left right check canon checkNext canonNext
        (fun _ seen _ _ _ _ => LocalOccurrenceThen profile ready base bindings start incoming seen (flatWordVisit finish)) before
  | .list element => fun item index checkNext canonNext finish before left right check canon =>
    ∃ entries, item = .dynamic (.list element) element entries ∧
      LiveCollectionOccurrenceEntry profile ready base bindings older destination inst (.list element) element entries index .flat
        checkNext canonNext start incoming left right before check canon
        (liveListTailPaths destination inst element entries index .flat
          (structuralMemoryOccurrencePaths profile ready base bindings older destination inst start incoming sink element)
          checkNext canonNext (fun seen _ _ _ _ => LocalOccurrenceThen profile ready base bindings start incoming seen (flatWordVisit finish))) sink
  | .map key element => fun item index checkNext canonNext finish before left right check canon =>
    let entryType : Stored.TypeOf := .record (ABI.mapEntryFields key element)
    ∃ entries, item = .dynamic (.map key element) entryType entries ∧
      LiveCollectionOccurrenceEntry profile ready base bindings older destination inst (.map key element) entryType entries index .flat
        checkNext canonNext start incoming left right before check canon
        (liveMapTailPaths (mapEntryOccurrencePaths profile ready base bindings older destination inst key element .flat start incoming
          (structuralMemoryOccurrencePaths profile ready base bindings older destination inst start incoming sink element))
          destination inst key element entries index .flat checkNext canonNext
          (fun seen _ _ _ _ => LocalOccurrenceThen profile ready base bindings start incoming seen (flatWordVisit finish))) sink
  | .fixedList element _ => flatAggregatePaths destination inst
      (structuralFlatOccurrencePaths profile ready base bindings older destination inst start incoming sink element)
  | .option element => flatSumPathsWith (fun visit seen _ _ _ _ =>
      LocalOccurrenceThen profile ready base bindings start incoming seen visit) destination.width
      (.option element) [none, some element]
      (fun _ => structuralFlatOccurrencePaths profile ready base bindings older destination inst start incoming sink element)
  | .result success failure =>
    let first := match success with
      | none => noFlatChild
      | some type => structuralFlatOccurrencePaths profile ready base bindings older destination inst start incoming sink type
    let second := match failure with
      | none => noFlatChild
      | some type => structuralFlatOccurrencePaths profile ready base bindings older destination inst start incoming sink type
    flatSumPathsWith (fun visit seen _ _ _ _ =>
      LocalOccurrenceThen profile ready base bindings start incoming seen visit) destination.width (.result success failure) [success, failure]
      (fun tag => if tag = 0 then first else second)
  | .variant cases => flatSumPathsWith (fun visit seen _ _ _ _ =>
      LocalOccurrenceThen profile ready base bindings start incoming seen visit) destination.width
      (.variant cases) (cases.map Prod.snd) (structuralFlatVariantOccurrencePaths profile ready base bindings older destination inst start incoming sink cases)
  | .record fields => flatAggregatePaths destination inst
      (selectFlatPaths (structuralFlatRecordOccurrencePaths profile ready base bindings older destination inst start incoming sink fields))
  | .tuple types => flatAggregatePaths destination inst
      (selectFlatPaths (structuralFlatTupleOccurrencePaths profile ready base bindings older destination inst start incoming sink types))
  | .own _ | .future _ | .stream _ | .errorContext => fun item index checkNext _ finish before left right check _ =>
    HandleOccurrenceThen profile ready base bindings start incoming left right before item index check checkNext (flatWordVisit finish) sink
  | _ => fun _ _ _ _ finish before _ _ _ _ =>
    LocalOccurrenceThen profile ready base bindings start incoming before (flatWordVisit finish)
termination_by structural type => type

def structuralFlatRecordOccurrencePaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (sink : RefusalSink grow sig) :
    List (String × Stored.TypeOf) → List (Stored.TypeOf × FlatFieldTrail grow sig)
  | [] => []
  | (_, type) :: rest =>
    (type, structuralFlatOccurrencePaths profile ready base bindings older destination inst start incoming sink type) ::
      structuralFlatRecordOccurrencePaths profile ready base bindings older destination inst start incoming sink rest
termination_by structural fields => fields

def structuralFlatTupleOccurrencePaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (sink : RefusalSink grow sig) :
    List Stored.TypeOf → List (Stored.TypeOf × FlatFieldTrail grow sig)
  | [] => []
  | type :: rest =>
    (type, structuralFlatOccurrencePaths profile ready base bindings older destination inst start incoming sink type) ::
      structuralFlatTupleOccurrencePaths profile ready base bindings older destination inst start incoming sink rest
termination_by structural types => types

def structuralFlatVariantOccurrencePaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (sink : RefusalSink grow sig) :
    List (String × Option Stored.TypeOf) → Nat → FlatFieldTrail grow sig
  | [], _ | (_, none) :: _, 0 => noFlatChild
  | (_, some type) :: _, 0 => structuralFlatOccurrencePaths profile ready base bindings older destination inst start incoming sink type
  | _ :: rest, tag + 1 => structuralFlatVariantOccurrencePaths profile ready base bindings older destination inst start incoming sink rest tag
termination_by structural cases => cases
end

mutual
def structuralFlatTransportPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (sink : RefusalSink grow sig) :
    Stored.TypeOf → FlatFieldTrail grow sig
  | .prim .string => fun item _ checkNext canonNext finish before left right check canon =>
    ∃ str : LinkedCallback.StringField, item = str.field ∧
      StringValueOccurrencePaths profile ready base bindings older destination inst str .flat start incoming left right check canon checkNext canonNext
        (fun _ _ _ _ _ _ => ∃ seen, LocalTransportThen profile ready base bindings start incoming seen (flatWordVisit finish)) before start incoming
  | .list element => fun item index checkNext canonNext finish before left right check canon =>
    ∃ entries, item = .dynamic (.list element) element entries ∧
      LiveCollectionOccurrenceEntry profile ready base bindings older destination inst (.list element) element entries index .flat
        checkNext canonNext start incoming left right before check canon
        (liveListTailPaths destination inst element entries index .flat
          (recursiveAllocatingTransportPaths profile ready base bindings older destination inst start incoming sink element)
          checkNext canonNext (fun seen _ _ _ _ => LocalTransportThen profile ready base bindings start incoming seen (flatWordVisit finish))) sink
  | .map key element => fun item index checkNext canonNext finish before left right check canon =>
    let entryType : Stored.TypeOf := .record (ABI.mapEntryFields key element)
    ∃ entries, item = .dynamic (.map key element) entryType entries ∧
      LiveCollectionOccurrenceEntry profile ready base bindings older destination inst (.map key element) entryType entries index .flat
        checkNext canonNext start incoming left right before check canon
        (liveMapTailPaths (mapEntryTransportPaths profile ready base bindings older destination inst key element .flat start incoming
          (recursiveAllocatingTransportPaths profile ready base bindings older destination inst start incoming sink element))
          destination inst key element entries index .flat checkNext canonNext
          (fun seen _ _ _ _ => LocalTransportThen profile ready base bindings start incoming seen (flatWordVisit finish))) sink
  | .fixedList element _ => flatAggregatePaths destination inst
      (structuralFlatTransportPaths profile ready base bindings older destination inst start incoming sink element)
  | .option element => flatSumPathsWith (fun visit seen _ _ _ _ =>
      LocalTransportThen profile ready base bindings start incoming seen visit) destination.width
      (.option element) [none, some element]
      (fun _ => structuralFlatTransportPaths profile ready base bindings older destination inst start incoming sink element)
  | .result success failure =>
    let first := match success with
      | none => noFlatChild
      | some type => structuralFlatTransportPaths profile ready base bindings older destination inst start incoming sink type
    let second := match failure with
      | none => noFlatChild
      | some type => structuralFlatTransportPaths profile ready base bindings older destination inst start incoming sink type
    flatSumPathsWith (fun visit seen _ _ _ _ =>
      LocalTransportThen profile ready base bindings start incoming seen visit) destination.width (.result success failure) [success, failure]
      (fun tag => if tag = 0 then first else second)
  | .variant cases => flatSumPathsWith (fun visit seen _ _ _ _ =>
      LocalTransportThen profile ready base bindings start incoming seen visit) destination.width
      (.variant cases) (cases.map Prod.snd) (structuralFlatVariantTransportPaths profile ready base bindings older destination inst start incoming sink cases)
  | .record fields => flatAggregatePaths destination inst
      (selectFlatPaths (structuralFlatRecordTransportPaths profile ready base bindings older destination inst start incoming sink fields))
  | .tuple types => flatAggregatePaths destination inst
      (selectFlatPaths (structuralFlatTupleTransportPaths profile ready base bindings older destination inst start incoming sink types))
  | .own _ | .future _ | .stream _ | .errorContext => fun item index checkNext _ finish before left right check _ =>
    HandleTransportThen profile ready base bindings start incoming left right before item index check checkNext (flatWordVisit finish) sink
  | _ => fun _ _ _ _ finish before _ _ _ _ =>
    LocalTransportThen profile ready base bindings start incoming before (flatWordVisit finish)
termination_by structural type => type

def structuralFlatRecordTransportPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (sink : RefusalSink grow sig) :
    List (String × Stored.TypeOf) → List (Stored.TypeOf × FlatFieldTrail grow sig)
  | [] => []
  | (_, type) :: rest =>
    (type, structuralFlatTransportPaths profile ready base bindings older destination inst start incoming sink type) ::
      structuralFlatRecordTransportPaths profile ready base bindings older destination inst start incoming sink rest
termination_by structural fields => fields

def structuralFlatTupleTransportPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (sink : RefusalSink grow sig) :
    List Stored.TypeOf → List (Stored.TypeOf × FlatFieldTrail grow sig)
  | [] => []
  | type :: rest =>
    (type, structuralFlatTransportPaths profile ready base bindings older destination inst start incoming sink type) ::
      structuralFlatTupleTransportPaths profile ready base bindings older destination inst start incoming sink rest
termination_by structural types => types

def structuralFlatVariantTransportPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (sink : RefusalSink grow sig) :
    List (String × Option Stored.TypeOf) → Nat → FlatFieldTrail grow sig
  | [], _ | (_, none) :: _, 0 => noFlatChild
  | (_, some type) :: _, 0 => structuralFlatTransportPaths profile ready base bindings older destination inst start incoming sink type
  | _ :: rest, tag + 1 => structuralFlatVariantTransportPaths profile ready base bindings older destination inst start incoming sink rest tag
termination_by structural cases => cases
end

/-- Compare either public body for arbitrary list/map nesting with fixed
arrays, heterogeneous aggregates, active sum arms, and nominal, scalar, or string leaves. -/
def LinkedRecursiveCollectionBody (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (incoming : Config (core3 grow) (HostState sig)) : Stored.TypeOf → Prop
  | .list element =>
    LinkedCollectionBody profile ready base bindings older site (.list element) element incoming (fun _ entries pointer bytes _ =>
      liveListTail profile ready base bindings site.destination site.inst element entries 0 route.output
        (liveCollectionField profile ready base bindings older site.destination site.inst element)
        site.reply site.referenceReply (fun _ => LinkedCallback.ChildFrameOver older) pointer bytes)
  | .map key element =>
    LinkedCollectionBody profile ready base bindings older site (.map key element) (.record (ABI.mapEntryFields key element)) incoming
      (fun _ entries pointer bytes _ => liveMapTailWith profile ready base bindings
        (liveCollectionMapEntry profile ready base bindings older site.destination site.inst key element route.output)
        site.destination site.inst key element entries 0 route.output
        (liveCollectionField profile ready base bindings older site.destination site.inst element)
        site.reply site.referenceReply (fun _ => LinkedCallback.ChildFrameOver older) pointer bytes)
  | _ => False

abbrev LinkedStringRecursiveMapBody (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (element : Stored.TypeOf) (incoming : Config (core3 grow) (HostState sig)) : Prop :=
  LinkedRecursiveCollectionBody profile ready base bindings older site incoming (.map .string element)

/-- Compare the descriptor and reached nominal value at the end of a
string-key replay. Late refusal leaves the value program unexecuted, even
when its first instruction is a flat-map width read. -/
def StringKeyNominalValue (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (origin : CStore (core3 grow)) (destination : RecordDestination) (inst : InstId) (element : Stored.TypeOf)
    (output : Stored.Lower.Output) (key : LinkedCallback.StringField) (value : Stored.Endpoints.RecordLower.Field)
    (address issueIndex : Nat) (left right : Config (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except Stored.Endpoints.RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Unit → Session grow sig (Ret (core3 grow))) : Prop :=
  open Stored.Endpoints.RecordLower ABI in
  let afterKey := address + (layout destination.width key.field.type).size
  let mode := CanonicalTree.EntryMode.forOutput destination.width (.map .string element) output
  let pending := mapValueProgram destination inst mode value afterKey canonNext
  let place := alignTo afterKey (layout destination.width value.type).alignment
  let report := fun verdict : Except Stored.Endpoints.RecordLower.Issue Unit => checkNext (verdict.mapError (.nested issueIndex))
  let checked := fun verdict : Except Stored.Endpoints.RecordLower.Issue Unit => (match verdict with
    | .error issue => pure (.error issue)
    | .ok () => OwnedMemory.Claims.Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst)
        destination.width value 1 (.memory place)) >>= report
  StringKeyReplay profile ready base bindings older origin destination inst key address left right check canon checked (fun _ => pending) →
  StringKeyThen profile ready base bindings older destination inst key address left right check canon checked (fun _ => pending)
    (fun _ lhs rhs cursor _ => CollectionSegment profile ready base bindings older lhs rhs cursor checkNext canonNext 0
      (· = pending) (fun reached => Core3.Grows origin.core reached.core))

/-- Cut the actual map traversal at its selected entry and preserve its exact
remainder. Both the successful continuation and the stopped suffix retain the
original traversal finish, which can publish the descriptor and reply. -/
def LinkedStringMapEntry (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (element : Stored.TypeOf) (entries : List Stored.Endpoints.RecordLower.Field)
    (index : Fin entries.length) (origin : CStore (core3 grow)) (basePtr : Nat)
    (left right : Config (core3 grow) (HostState sig)) (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except Stored.Endpoints.RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Unit → Session grow sig (Ret (core3 grow)))
    (next : Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
      PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → Prop :=
        fun lhs _ _ _ => Core3.Grows origin.core lhs.store.core) : Prop :=
  open Stored.Endpoints.RecordLower ABI in
  let destination := site.destination
  let cx := destination.context site.inst
  let type : Stored.TypeOf := .record (mapEntryFields .string element)
  let stride := (layout destination.width type).size
  let ptr := basePtr + index.val * stride
  let mode := CanonicalTree.EntryMode.forOutput destination.width (.map .string element) route.output
  let item := entries[index.val]
  let rest := entries.drop (index.val + 1)
  let checkTail := fun verdict : Except Stored.Endpoints.RecordLower.Issue Unit => (match verdict with
    | .error issue => pure (.error issue)
    | .ok () => OwnedMemory.Claims.Record.Effects.elements recordClaims Limits.spec Quirks.none cx destination.width
        rest stride (ptr + stride) (index.val + 1)) >>= checkNext
  let canonTail := fun (_ : Unit) => CanonicalTree.elements Limits.spec Quirks.none cx destination.width
    rest mode stride (ptr + stride) >>= canonNext
  left.ctl = check.control (OwnedMemory.Claims.Record.Effects.elements recordClaims Limits.spec Quirks.none cx
    destination.width (entries.drop index.val) stride ptr index.val >>= checkNext) →
  right.ctl = canon.control (CanonicalTree.elements Limits.spec Quirks.none cx destination.width
    (entries.drop index.val) mode stride ptr >>= canonNext) →
  ∃ (key : LinkedCallback.StringField) (value : Field), item = .aggregate type [key.field, value] ∧
    let keyArea := layout destination.width key.field.type
    let keyPtr := alignTo ptr keyArea.alignment
    let afterKey := keyPtr + keyArea.size
    let pending := mapValueProgram destination site.inst mode value afterKey canonTail
    let valuePtr := alignTo afterKey (layout destination.width value.type).alignment
    let report := fun verdict : Except Stored.Endpoints.RecordLower.Issue Unit => checkTail (verdict.mapError (.nested index.val))
    let checked := fun verdict : Except Stored.Endpoints.RecordLower.Issue Unit => (match verdict with
      | .error issue => pure (.error issue)
      | .ok () => OwnedMemory.Claims.Record.Effects.field recordClaims Limits.spec Quirks.none cx destination.width
          value 1 (.memory valuePtr)) >>= report
    StringKeyThen profile ready base bindings older destination site.inst key keyPtr left right check canon checked (fun _ => pending)
      (fun _ lhs rhs cursor _ => CollectionSegmentThen profile ready base bindings older lhs rhs cursor checkTail canonTail 0
        (· = pending) (fun _ reached peer nextCheck => next reached peer cursor nextCheck))

/-- Exact controls for a reached suffix, including the original finish. -/
def LinkedStringMapAt {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route) (element : Stored.TypeOf)
    (entries : List Stored.Endpoints.RecordLower.Field) (index basePtr : Nat)
    (left right : Config (core3 grow) (HostState sig)) (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except Stored.Endpoints.RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Unit → Session grow sig (Ret (core3 grow))) : Prop :=
  open Stored.Endpoints.RecordLower ABI in
  let stride := (layout site.destination.width (.record (mapEntryFields .string element))).size
  let address := basePtr + index * stride
  let cx := site.destination.context site.inst
  let mode := CanonicalTree.EntryMode.forOutput site.destination.width (.map .string element) route.output
  left.ctl = check.control (OwnedMemory.Claims.Record.Effects.elements recordClaims Limits.spec Quirks.none cx
    site.destination.width (entries.drop index) stride address index >>= checkNext) ∧
  right.ctl = canon.control (CanonicalTree.elements Limits.spec Quirks.none cx site.destination.width
    (entries.drop index) mode stride address >>= canonNext)

/-- Compare a suffix of the actual map traversal. Only a returned key and
value enter the next suffix; a suspended allocator, refusal or trap does not.
Each link retains its visible trace and the trails of older occurrences. -/
def LinkedStringMapTraversal (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (element : Stored.TypeOf) (entries : List Stored.Endpoints.RecordLower.Field)
    (index : Nat) (origin : CStore (core3 grow)) (basePtr : Nat)
    (left right : Config (core3 grow) (HostState sig)) (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except Stored.Endpoints.RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Unit → Session grow sig (Ret (core3 grow)))
    (finish : Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
      PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → Prop :=
        fun _ _ _ _ => True) : Prop :=
  LinkedStringMapAt site element entries index basePtr left right check canon checkNext canonNext ∧
    if present : index < entries.length then
      LinkedStringMapEntry profile ready base bindings older site element entries ⟨index, present⟩ origin basePtr
        left right check canon checkNext canonNext (fun lhs rhs cursor peer =>
          LinkedStringMapTraversal profile ready base bindings older site element entries (index + 1) origin basePtr
            lhs rhs cursor peer checkNext canonNext finish)
    else
      LinkedCallback.ChildFrameOver older left right check canon ∧
        left.ctl = check.control (checkNext (.ok ())) ∧ right.ctl = canon.control (canonNext ()) ∧
        Core3.Grows origin.core left.store.core ∧ finish left right check canon
termination_by entries.length - index

/-- The actual post-prepare map body for either public give. Only a complete
entry traversal executes the outer descriptor, which can itself trap. -/
def LinkedStringMapBody (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (element : Stored.TypeOf) (entries : List Stored.Endpoints.RecordLower.Field)
    (basePtr : Nat) (left right : Config (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (index : Nat := 0) (origin : CStore (core3 grow) := left.store) : Prop :=
  let publish : Session grow sig route.output.Result := Stored.Endpoints.ListLower.publish
    (site.destination.context site.inst) site.destination.width basePtr entries.length route.output
  let checkTail := PayloadPrefix.checkedSequenceNext (.nested 0) (fun (_ : Unit) => publish >>= fun value => pure (.ok value)) site.reply
  let canonTail := fun (_ : Unit) => publish >>= site.referenceReply
  LinkedStringMapTraversal profile ready base bindings older site element entries index origin basePtr left right check canon
    checkTail canonTail (fun lhs rhs cursor _ =>
      CollectionSegment profile ready base bindings older lhs rhs cursor site.reply site.referenceReply 0 (fun _ => False))

def mapValueSuffix (destination : RecordDestination) (inst : InstId)
    (mode : Stored.Endpoints.RecordLower.CanonicalTree.EntryMode)
    (keyField value : Stored.Endpoints.RecordLower.Field) (rest : List Stored.Endpoints.RecordLower.Field) (stride address : Nat)
    (finish : Unit → Session grow sig (Ret (core3 grow))) : Session grow sig (Ret (core3 grow)) :=
  open Stored.Endpoints.RecordLower ABI in
  let keyArea := layout destination.width keyField.type
  let keyPtr := alignTo address keyArea.alignment
  let cx := destination.context inst
  mapFieldPlacement cx mode fun reached =>
    let valPtr := alignTo (keyPtr + keyArea.size) (layout reached value.type).alignment
    CanonicalTree.field Limits.spec Quirks.none cx destination.width value (.memory valPtr) >>= fun _ =>
      CanonicalTree.elements Limits.spec Quirks.none cx destination.width rest mode stride (address + stride) >>= finish

/-- A map value guard stops after its key has run. Flat maps still have the
reached value-width read ahead of them; memory maps use allocation-time placement. -/
def MapValueStop (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType) (element : Stored.TypeOf)
    (mode : Stored.Endpoints.RecordLower.CanonicalTree.EntryMode)
    (entries : List Stored.Endpoints.RecordLower.Field) (stride ptr : Nat)
    (finish : Unit → Session grow sig (Ret (core3 grow))) (stop : Session grow sig (Ret (core3 grow))) : Prop :=
  ∃ leading rest keyField value,
    entries = leading ++ .aggregate (.record (ABI.mapEntryFields key element)) [keyField, value] :: rest ∧
    stop = mapValueSuffix destination inst mode keyField value rest stride (ptr + leading.length * stride) finish

/-- A reached map can stop before entries at fresh preparation, or
after the key of the value currently being visited. -/
def MapReturnStop (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType) (element : Stored.TypeOf)
    (entries : List Stored.Endpoints.RecordLower.Field) (output : Stored.Lower.Output) (ptr : Nat)
    (finish : output.Result → Session grow sig (Ret (core3 grow))) (stop : Session grow sig (Ret (core3 grow))) : Prop :=
  open Stored.Endpoints.RecordLower ABI in
  let area := layout destination.width (.record (mapEntryFields key element))
  let mode := CanonicalTree.EntryMode.forOutput destination.width (.map key element) output
  stop = (PayloadPrefix.canonicalCollectionTail destination inst entries area output ptr mode >>= finish) ∨
  MapValueStop destination inst key element mode entries area.size ptr
    (fun _ => Stored.Endpoints.ListLower.publish (destination.context inst) destination.width ptr entries.length output >>= finish) stop

/-- Complete the actual public replies from a reached allocator return.
Only a returned descriptor rejoins both machines. A typed refusal records
the checked completion and rejoins its caller, leaving canonical suspended
at the actually reached program. A canonical trap executes no reply. -/
def CollectionSegmentReplies (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (checked canonical : Config (core3 grow) (HostState sig))
    (stopsAt : Session grow sig (Ret (core3 grow)) → Prop) (offset : Nat := 1)
    (afterReturn : Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) → Prop := fun _ _ => True) : Prop :=
  ∃ (outcome : PayloadPrefix.Outcome route.output.Result) (checkLabels canonLabels : Trace grow sig)
    (left right : Config (core3 grow) (HostState sig)),
    Steps profile ready (specDispatch ready base) checked checkLabels left ∧
    Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) canonical canonLabels right ∧
    left.store = right.store ∧ PayloadPrefix.visible checkLabels = PayloadPrefix.visible canonLabels ∧
    match outcome with
    | .returned value => ∃ before canonBefore checkBody canonBody,
        checkLabels = checkBody ++ [.tau, .tau, .tau] ∧ canonLabels = canonBody ++ [.tau] ∧
        Steps profile ready (specDispatch ready base) checked checkBody before ∧
        Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) canonical canonBody canonBefore ∧
        (∀ dispatch, Steps profile ready dispatch before [.tau, .tau, .tau] left) ∧
        (∀ dispatch, Steps profile ready dispatch canonBefore [.tau] right) ∧
        left.host = before.host.record (route.reply site.destination site.start.host.nextTicket (.ok value)).1 ∧
        right.host = canonBefore.host ∧ HostFrame.Related.Paired older left right ∧ afterReturn left right ∧
        (∀ depth, ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready base)
          checked (.active 0 (depth + 1 + offset)) checkLabels left (.active 0 depth)) ∧
        (∀ depth, ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base))
          canonical (.active 0 (depth + 1 + offset)) canonLabels right (.active 0 depth))
    | .refused issue => ∃ (before : Config (core3 grow) (HostState sig)) (checkBody : Trace grow sig)
        (canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
        (stop : Session grow sig (Ret (core3 grow))), stopsAt stop ∧
        checkLabels = checkBody ++ [.tau, .tau, .tau] ∧
        Steps profile ready (specDispatch ready base) checked checkBody before ∧
        (∀ depth, ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base))
          canonical (.active 0 (depth + offset)) canonLabels right (.active 0 depth)) ∧
        left.host = before.host.record (route.reply site.destination site.start.host.nextTicket (.error issue)).1 ∧
        (∀ dispatch, Steps profile ready dispatch before [.tau, .tau, .tau] left) ∧ right.ctl = canon.control stop ∧
        (∀ depth, ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready base)
          checked (.active 0 (depth + 1 + offset)) checkLabels left (.active 0 depth))
    | .trapped reason => left.ctl = [] ∧ right.ctl = [] ∧ ∃ leading, PayloadPrefix.visible canonLabels = leading ++ [.trap reason]

/-- The error program has already reached the public reply on checked.
Only that machine runs a completion; the canonical path ends at the exact
configuration supplied by the traversal. -/
def publicRefusalSink (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (entered : Config (core3 grow) (HostState sig)) : RefusalSink grow sig where
  admits next := ∀ issue, ∃ reported, next issue = site.reply (.error reported)
  nested _ closed index issue := closed (.nested index issue)
  exit next issue observed lhs rhs cursor :=
    ∃ reported, next issue = site.reply (.error reported) ∧
      ComparedSlots profile ready base bindings site.checked entered observed lhs rhs ∧ lhs.store = rhs.store ∧
      ∃ (segments : List (Seg (core3 grow) (HostState sig))) (checkBody canonBody : Trace grow sig),
        let reply := route.reply site.destination site.start.host.nextTicket (.error reported)
        let resumed :=
          { lhs with
            host := lhs.host.record reply.1
            ctl := ⟨cursor.thread, .core ((core3 grow).resume lhs.store.core site.core (.values reply.2)) site.resume,
              segments⟩ :: cursor.rest }
        PayloadPrefix.visible checkBody = observed ∧ PayloadPrefix.visible canonBody = observed ∧
        (∀ dispatch place, ReturnFrame.Occurrence.Trail profile ready dispatch lhs (some place) [.tau, .tau, .tau] resumed
          ((ReturnFrame.Occurrence.Edit.pop : ReturnFrame.Occurrence.Edit (core3 grow) (HostState sig)).follow place)) ∧
        (∀ depth, ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready base)
          site.checked (.active 0 (depth + 1)) (checkBody ++ [.tau, .tau, .tau]) resumed (.active 0 depth)) ∧
        (∀ depth, ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base))
          entered (.active 0 depth) canonBody rhs (.active 0 depth))

/-- From actual collection allocation and placement, visit the reached
descendants in order. The cumulative trail supports either original caller
rejoins after publication or a checked-only refusal reply at a reached
nested guard. A trap or finite suspension need not reach either reply. -/
def LinkedCollectionRejoinPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (incoming : Config (core3 grow) (HostState sig)) : Stored.TypeOf → Prop
  | .list element =>
    LinkedCollectionBody profile ready base bindings older site (.list element) element incoming fun entered entries =>
      liveListTailPaths site.destination site.inst element entries 0 route.output
        (liveRecursivePaths profile ready base bindings older site.destination site.inst site.checked entered 0
          (publicRefusalSink profile ready base bindings site entered) element)
        site.reply site.referenceReply
        (fun _ _ _ _ _ => CollectionSegmentReplies profile ready base bindings older site site.checked entered (fun _ => False) 0)
  | .map key element =>
    LinkedCollectionBody profile ready base bindings older site (.map key element) (.record (ABI.mapEntryFields key element)) incoming
      fun entered entries => liveMapTailPaths (liveMapEntryPaths profile ready base bindings older site.destination site.inst key element
        route.output site.checked entered 0 (liveRecursivePaths profile ready base bindings older site.destination site.inst site.checked entered 0
          (publicRefusalSink profile ready base bindings site entered) element))
        site.destination site.inst key element entries 0 route.output site.reply site.referenceReply
        (fun _ _ _ _ _ => CollectionSegmentReplies profile ready base bindings older site site.checked entered (fun _ => False) 0)
  | _ => False

/-- The same reached string plan can return words or store a descriptor.
On a finite allocator prefix the occurrence remains available without a reply. -/
def LinkedStringRejoinPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (incoming : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ str leading entered peer,
    site.field = str.field ∧ PayloadPrefix.visible leading = [] ∧
    (∀ place, ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base))
      incoming place leading entered
      (((ReturnFrame.Occurrence.Edit.push (.core site.core site.resume)).follow place).getD place)) ∧
    entered.host = incoming.host ∧
    StringValuePaths profile ready base bindings older site.destination site.inst str route.output
      site.checked entered site.checked entered site.cursor peer site.reply site.referenceReply
      (fun _ _ _ _ _ _ => CollectionSegmentReplies profile ready base bindings older site site.checked entered (fun _ => False) 0)
      [] 0

/-- The successful body continuation of a memory give is already the
actual public reply; there is no separate root descriptor to publish. -/
def MemoryRootFinish (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {pointer : FlatValue}
    (site : PayloadRoot.Site grow sig (.memory pointer)) : LinkedCallback.MemorySequence.Finish grow sig :=
  fun left right check canon => LinkedCallback.ChildFrameOver older left right check canon ∧
    left.ctl = check.control (site.reply (.ok ())) ∧ right.ctl = canon.control (site.referenceReply ())

/-- Enter the actual canonical memory root and compare the same compiled
field traversal used for children. Success and typed refusal target the
original caller, while trap and allocator cuts stay at their reached sites. -/
def LinkedMemoryRejoinPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {pointer : FlatValue}
    (site : PayloadRoot.Site grow sig (.memory pointer)) (incoming : Config (core3 grow) (HostState sig))
    (afterReturn : Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) → Prop := fun _ _ => True) : Prop :=
  ∃ leading entered peer, PayloadPrefix.visible leading = [] ∧
    (∀ place, ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base))
      incoming place leading entered
      (((ReturnFrame.Occurrence.Edit.push (.core site.core site.resume)).follow place).getD place)) ∧
    entered.host = incoming.host ∧
    liveRecursivePaths profile ready base bindings older site.destination site.inst site.checked entered 0
      (publicRefusalSink profile ready base bindings site entered) (sig.payload site.tag)
      site.field 0 (flatNat pointer) site.reply site.referenceReply
      (fun _ _ _ _ _ => CollectionSegmentReplies profile ready base bindings older site site.checked entered (fun _ => False) 0 afterReturn)
      [] site.checked entered site.cursor peer

/-- The original flat public entry and cumulative traversal. Only successful
children contribute words; a typed refusal runs the checked reply alone. -/
def LinkedFlatAggregateRejoinPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {type : Stored.TypeOf}
    (site : PayloadRoot.Site grow sig (.flat type)) (incoming : Config (core3 grow) (HostState sig))
    (afterReturn : Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) → Prop := fun _ _ => True) : Prop :=
  ∃ leading entered peer, PayloadPrefix.visible leading = [] ∧
    (∀ place, ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base))
      incoming place leading entered
      (((ReturnFrame.Occurrence.Edit.push (.core site.core site.resume)).follow place).getD place)) ∧
    entered.host = incoming.host ∧
    liveFlatPaths profile ready base bindings older site.destination site.inst site.checked entered 0
      (publicRefusalSink profile ready base bindings site entered) (sig.payload site.tag)
      site.field 0 site.reply site.referenceReply
      (fun _ _ _ _ _ _ => CollectionSegmentReplies profile ready base bindings older site site.checked entered (fun _ => False) 0 afterReturn)
      [] site.checked entered site.cursor peer

/-- The installed caller's mark is separate from older request origins. If
it is not at the reached reply slot, the relation records its actual
coordinate or loss instead of asserting a rejoin of the original caller. -/
def PublicOccurrenceExit (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (entered : Config (core3 grow) (HostState sig))
    (verdict : Except Stored.Endpoints.RecordLower.Issue route.output.Result) (seen : Trace grow sig)
    (left right : Config (core3 grow) (HostState sig)) : Prop :=
  open ReturnFrame.Occurrence in
  ∃ checkBody canonBody mark,
    CoupledOccurrencePaths profile ready base bindings site.checked entered checkBody canonBody left right ∧
    PayloadPrefix.visible checkBody = seen ∧ PayloadPrefix.visible canonBody = seen ∧ left.store = right.store ∧
    Trail profile ready (specDispatch ready base) site.checked (some (.active 0 0)) checkBody left mark ∧
    Trail profile ready (specDispatch ready (LiveDispatch.host bindings base)) entered (some (.active 0 0)) canonBody right mark ∧
    (mark = some (.active 0 0) →
      let reply := route.reply site.destination site.start.host.nextTicket verdict
      ∃ checked canonical,
        checked.host = left.host.record reply.1 ∧
        (∀ place, Trail profile ready (specDispatch ready base) left (some place) [.tau, .tau, .tau] checked
          ((Edit.pop : Edit (core3 grow) (HostState sig)).follow place)) ∧
        match verdict with
        | .error _ => canonical = right
        | .ok _ => canonical.host = right.host ∧ HostFrame.Related.Paired older checked canonical ∧
          ∀ place, Trail profile ready (specDispatch ready (LiveDispatch.host bindings base)) right (some place) [.tau] canonical
            ((Edit.pop : Edit (core3 grow) (HostState sig)).follow place))

/-- After a checked-only reply the corresponding older origins can be at
different positions. Both still follow their own reached machine path. -/
def RequestExitOccurrences (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (start incoming : Config (core3 grow) (HostState sig)) (seen : Trace grow sig)
    (checked canonical : Config (core3 grow) (HostState sig)) : Prop :=
  open ReturnFrame.Occurrence in
  ∃ checkLabels canonLabels, PayloadPrefix.visible checkLabels = seen ∧ PayloadPrefix.visible canonLabels = seen ∧
    ∀ mark : Location, ∃ leftMark rightMark,
      Trail profile ready (specDispatch ready base) start (some mark) checkLabels checked leftMark ∧
      Trail profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming (some mark) canonLabels canonical rightMark

def RequestExitKind (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {α : Type}
    (verdict : Except Stored.Endpoints.RecordLower.Issue α) (stopped checked canonical : Config (core3 grow) (HostState sig)) : Prop :=
  match verdict with
  | .error _ => canonical = stopped
  | .ok _ => HostFrame.Related.Paired older checked canonical

def publicOccurrenceSink (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (entered : Config (core3 grow) (HostState sig)) : RefusalSink grow sig where
  admits next := ∀ issue, ∃ reported, next issue = site.reply (.error reported)
  nested _ closed index issue := closed (.nested index issue)
  exit next issue seen left right _ := ∃ reported, next issue = site.reply (.error reported) ∧
    PublicOccurrenceExit profile ready base bindings older site entered (.error reported) seen left right

/-- Keep the reached refused continuation and attach a local observation
of the typed error at the same checked/canonical cut. -/
def publicOccurrenceSinkWith (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (entered : Config (core3 grow) (HostState sig))
    (refused : Stored.Endpoints.RecordLower.Issue → Trace grow sig →
      Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) → Prop) : RefusalSink grow sig :=
  { publicOccurrenceSink profile ready base bindings older site entered with
    exit := fun next issue seen left right _ => ∃ reported, next issue = site.reply (.error reported) ∧
      PublicOccurrenceExit profile ready base bindings older site entered (.error reported) seen left right ∧
      refused reported seen left right }

/-- The flat body resolves each reached compiled field and accumulates older
active and saved tracks all the way to the actual public reply. The canonical
entry retains its paths from the live original request. -/
def LinkedFlatOccurrenceBody (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {type : Stored.TypeOf}
    (site : PayloadRoot.Site grow sig (.flat type)) (incoming : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ canonLabels entered peer, PayloadPrefix.visible canonLabels = [] ∧
    (∀ place, ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base))
      incoming place canonLabels entered (site.entryPlace place)) ∧ entered.host = incoming.host ∧
    structuralFlatOccurrencePaths profile ready base bindings older site.destination site.inst site.checked entered
      (publicOccurrenceSink profile ready base bindings older site entered) (sig.payload site.tag)
      site.field 0 site.reply site.referenceReply
      (fun words seen left right _ _ => PublicOccurrenceExit profile ready base bindings older site entered (.ok words) seen left right)
      [] site.checked entered site.cursor peer

/-- The memory body uses the same exit relation as flat lowering. Each
child visits the real memory program and contributes its reached paths. -/
def LinkedMemoryOccurrenceBody (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {pointer : FlatValue}
    (site : PayloadRoot.Site grow sig (.memory pointer)) (incoming : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ canonLabels entered peer, PayloadPrefix.visible canonLabels = [] ∧
    (∀ place, ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base))
      incoming place canonLabels entered (site.entryPlace place)) ∧ entered.host = incoming.host ∧
    structuralMemoryOccurrencePaths profile ready base bindings older site.destination site.inst site.checked entered
      (publicOccurrenceSink profile ready base bindings older site entered) (sig.payload site.tag)
      site.field 0 (flatNat pointer) site.reply site.referenceReply
      (fun seen left right _ _ => PublicOccurrenceExit profile ready base bindings older site entered (.ok ()) seen left right)
      [] site.checked entered site.cursor peer

/-- At a successful body endpoint, carry every older occurrence from the
original request. Only the reached original caller at the top licenses
the checked completion and common Core return. -/
def PublicSuccessTransport (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (incoming entered : Config (core3 grow) (HostState sig))
    (checkEntry canonEntry : Trace grow sig) (value : route.output.Result) (seen : Trace grow sig)
    (left right : Config (core3 grow) (HostState sig)) : Prop :=
  open ReturnFrame.Occurrence in
  ∃ checkBody canonBody mark,
    PayloadPrefix.visible checkBody = seen ∧ PayloadPrefix.visible canonBody = seen ∧
    OccurrenceTransport profile ready base bindings site.start incoming (checkEntry ++ checkBody) (canonEntry ++ canonBody)
      left right [mark] ∧
    Trail profile ready (specDispatch ready base) site.checked (some (.active 0 0)) checkBody left mark ∧
    Trail profile ready (specDispatch ready (LiveDispatch.host bindings base)) entered (some (.active 0 0)) canonBody right mark ∧
    VisitorWriterPath profile ready base bindings site.start incoming checkEntry canonEntry site.checked entered ∧
    (mark = some (.active 0 0) → ∃ checked canonical,
      checked.host = left.host.record (route.reply site.destination site.start.host.nextTicket (.ok value)).1 ∧
      canonical.host = right.host ∧ HostFrame.Related.Paired older checked canonical ∧
      OccurrenceTransport profile ready base bindings site.start incoming
        ((checkEntry ++ checkBody) ++ [.tau, .tau, .tau]) ((canonEntry ++ canonBody) ++ [.tau]) checked canonical ∧
      VisitorWriterPath profile ready base bindings left right [.tau, .tau, .tau] [.tau] checked canonical ∧
      (∀ {tail stopped}, Steps profile ready (specDispatch ready base) left tail stopped → tail.length < 3 →
        CheckedCoreReplyPrefix profile ready (specDispatch ready base) left tail stopped))

/-- The terminal observation is inside the recursive visitor, so it is
applied only at a reached success, not at a trap, refusal or suspension. -/
def LinkedMemoryTransportBodyWith (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {pointer : FlatValue}
    (site : PayloadRoot.Site grow sig (.memory pointer)) (incoming : Config (core3 grow) (HostState sig))
    (success : Trace grow sig → Trace grow sig → Config (core3 grow) (HostState sig) → Trace grow sig →
      Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) → Prop)
    (refused : Trace grow sig → Trace grow sig → Config (core3 grow) (HostState sig) →
      Stored.Endpoints.RecordLower.Issue → Trace grow sig →
      Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) → Prop) : Prop :=
  ∃ canonLabels entered peer, PayloadPrefix.visible canonLabels = [] ∧
    (∀ place, ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base))
      incoming place canonLabels entered (site.entryPlace place)) ∧ entered.host = incoming.host ∧
    ∀ checkLabels, site.EntryPrefix profile ready base checkLabels site.checked →
      Plain.HostFramedSteps HostState.writer profile ready (specDispatch ready base) site.start checkLabels site.checked →
      site.PreparedEntry profile ready base checkLabels →
      recursiveAllocatingTransportPaths profile ready base bindings older site.destination site.inst site.checked entered
        (publicOccurrenceSinkWith profile ready base bindings older site entered (refused checkLabels canonLabels entered)) (sig.payload site.tag)
        site.field 0 (flatNat pointer) site.reply site.referenceReply
        (fun seen left right _ _ => success checkLabels canonLabels entered seen left right)
        [] site.checked entered site.cursor peer

/-- The checked entry prefix is supplied by the placed branch of the cut.
The recursive visitor derives the terminal observation from reached paths. -/
def LinkedMemoryTransportBody (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {pointer : FlatValue}
    (site : PayloadRoot.Site grow sig (.memory pointer)) (incoming : Config (core3 grow) (HostState sig)) : Prop :=
  LinkedMemoryTransportBodyWith profile ready base bindings older site incoming
    (fun checkEntry canonEntry entered seen left right =>
      PublicSuccessTransport profile ready base bindings older site incoming entered checkEntry canonEntry () seen left right)
    (fun _ _ _ _ _ _ _ => True)

/-- The reached flat visitor keeps emitted words and occurrence transport
through the real fold, rather than a separately supplied body trail. -/
def LinkedFlatTransportBodyWith (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {type : Stored.TypeOf}
    (site : PayloadRoot.Site grow sig (.flat type)) (incoming : Config (core3 grow) (HostState sig))
    (success : Trace grow sig → Trace grow sig → Config (core3 grow) (HostState sig) → List FlatValue → Trace grow sig →
      Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) → Prop)
    (refused : Trace grow sig → Trace grow sig → Config (core3 grow) (HostState sig) →
      Stored.Endpoints.RecordLower.Issue → Trace grow sig →
      Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) → Prop) : Prop :=
  ∃ canonLabels entered peer, PayloadPrefix.visible canonLabels = [] ∧
    (∀ place, ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base))
      incoming place canonLabels entered (site.entryPlace place)) ∧ entered.host = incoming.host ∧
    ∀ checkLabels, site.EntryPrefix profile ready base checkLabels site.checked →
      Plain.HostFramedSteps HostState.writer profile ready (specDispatch ready base) site.start checkLabels site.checked →
      site.PreparedEntry profile ready base checkLabels →
      structuralFlatTransportPaths profile ready base bindings older site.destination site.inst site.checked entered
        (publicOccurrenceSinkWith profile ready base bindings older site entered (refused checkLabels canonLabels entered)) (sig.payload site.tag)
        site.field 0 site.reply site.referenceReply
        (fun words seen left right _ _ => success checkLabels canonLabels entered words seen left right)
        [] site.checked entered site.cursor peer

/-- The actual range verdict after an allocator return. A late reservation
refusal runs only the checked completion; canonical is at child entry with
the reached store, before any element write or descriptor publication. -/
def CollectionReturnFailure (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (type element : Stored.TypeOf)
    (entries : List Stored.Endpoints.RecordLower.Field) (pointer : Nat)
    (checked canonical : Config (core3 grow) (HostState sig))
    (check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) : Prop :=
  open Stored.Endpoints.RecordLower ABI PayloadPrefix in
  let area := layout site.destination.width element
  let mode := CanonicalTree.EntryMode.forOutput site.destination.width type route.output
  let checkedDispatch := specDispatch ready base
  let canonDispatch := specDispatch ready (LiveDispatch.host bindings base)
  let trap := fun reason => ∃ leftCount rightCount,
    Steps profile ready checkedDispatch checked (List.replicate leftCount .tau ++ [.trap reason]) (StepDefs.trapCfg checked) ∧
    Steps profile ready canonDispatch canonical (List.replicate rightCount .tau ++ [.trap reason]) (StepDefs.trapCfg canonical)
  checked.store = canonical.store ∧ ∃ bytes,
    (core3 grow).memSize? checked.store.core site.destination.memory = some bytes ∧
    if pointer ≠ alignTo pointer area.alignment then trap .unalignedPointer
    else if pointer + entries.length * area.size ≤ bytes then
      ∀ issue, OwnedMemory.Claims.Record.prepare checked.store checked.host.writer (Field.listObjects entries) = .error issue →
        let child := canonicalCollectionTail site.destination site.inst entries area route.output pointer mode >>= site.referenceReply
        let reply := route.reply site.destination site.start.host.nextTicket (.error (LinkedCallback.CollectionVisit.afterAllocation 0 issue))
        ∃ (canon : Cursor (E := core3 grow) (HostState sig)) (lhs rhs : Trace grow sig)
          (segments : List (Seg (core3 grow) (HostState sig))),
          visible lhs = [] ∧ visible rhs = [] ∧
          Steps profile ready checkedDispatch checked (lhs ++ [.tau, .tau, .tau])
            { checked with
              host := checked.host.record reply.1
              ctl := ⟨check.thread, .core ((core3 grow).resume checked.store.core site.core (.values reply.2)) site.resume,
                segments⟩ :: check.rest } ∧
          ReturnFrame.Occurrence.RetainsBelowTop profile ready canonDispatch canonical rhs
            { canonical with ctl := canon.control child }
    else trap .outOfBounds

/-- Classify each finite supported root callback prefix. Only an actual
return of the installed allocator occurrence can enter the failure cut. -/
def LinkedCollectionReturnFailures (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (incoming : Config (core3 grow) (HostState sig))
    (type element : Stored.TypeOf) : Prop :=
  open Stored.Endpoints.RecordLower ABI PayloadPrefix in
  ∃ (entries : List Field) (leading : Trace grow sig) (entered : Config (core3 grow) (HostState sig))
    (peer : Cursor (E := core3 grow) (HostState sig)),
    site.field = .dynamic type element entries ∧ visible leading = [] ∧
    (∀ place, ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base))
      incoming place leading entered
      (((ReturnFrame.Occurrence.Edit.push (.core site.core site.resume)).follow place).getD place)) ∧
    let area := layout site.destination.width element
    let mode := CanonicalTree.EntryMode.forOutput site.destination.width type route.output
    let lhs := checkedCollectionResume site.destination site.inst entries area 0 route.output site.reply
    let rhs := canonicalCollectionResume site.destination site.inst entries area route.output site.referenceReply mode
    let checkedEntry := collectionEntry site.destination site.inst area entries.length (specDispatch ready base) site.checked site.cursor lhs
    let canonEntry := collectionEntry site.destination site.inst area entries.length
      (specDispatch ready (LiveDispatch.host bindings base)) entered peer rhs
    ∀ {seen checked}, ClosedCallbackPrefix bindings profile ready base
        (fun resume => (∃ other, older resume other) ∨ resume = lhs) checkedEntry seen checked →
      ∃ checkLabels canonLabels canonical mark,
        AllocatorMark profile ready base bindings older checkedEntry canonEntry checkLabels canonLabels checked canonical mark ∧
        ComparedPaths profile ready base bindings site.checked entered seen checked canonical ∧
        ∀ pointer cursor, mark = some (.active 0 0) →
          checked.ctl = { cursor with frames := .prog lhs :: cursor.frames }.control (.pure (.nat pointer)) →
          CollectionReturnFailure profile ready base bindings site type element entries pointer checked canonical cursor

/-- A marked string-key map return either traps or refuses before any entry,
or reaches the recursive body with the original checked caller still tracked. -/
def LinkedStringMapReturn (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (element : Stored.TypeOf) (entries : List Stored.Endpoints.RecordLower.Field)
    (pointer : Nat) (checked canonical : Config (core3 grow) (HostState sig))
    (check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) : Prop :=
  open ReturnFrame.Occurrence in
  let checkedDispatch := specDispatch ready base
  let canonDispatch := specDispatch ready (LiveDispatch.host bindings base)
  CollectionSegmentReplies profile ready base bindings older site checked canonical
    (MapReturnStop site.destination site.inst .string element entries route.output pointer site.referenceReply) ∨
  ∃ (left right : Config (core3 grow) (HostState sig)) (canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (checkLabels canonLabels callerLabels : Trace grow sig),
    RetainsBelowTop profile ready checkedDispatch checked checkLabels left ∧
    RetainsBelowTop profile ready canonDispatch canonical canonLabels right ∧
    PayloadPrefix.visible checkLabels = PayloadPrefix.visible canonLabels ∧
    Prefix profile ready checkedDispatch site.checked (.active 0 0) callerLabels left (.active 0 0) ∧
    LinkedStringMapBody profile ready base bindings older site element entries pointer left right check canon

/-- A traversal rooted at the prepared public body. Every reached allocator
prefix has a cumulative comparison. A completed entry advances to the actual
next suffix; a terminal segment carries the original caller result. -/
def LinkedStringMapPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (element : Stored.TypeOf) (entries : List Stored.Endpoints.RecordLower.Field)
    (index basePtr : Nat) (leftStart rightStart left right : Config (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) (seen : Trace grow sig) (offset : Nat := 0) : Prop :=
  open Stored.Endpoints.RecordLower ABI PayloadPrefix ReturnFrame.Occurrence in
  let destination := site.destination
  let cx := destination.context site.inst
  let type : Stored.TypeOf := .record (mapEntryFields .string element)
  let stride := (layout destination.width type).size
  let publish : Session grow sig route.output.Result := Stored.Endpoints.ListLower.publish cx destination.width basePtr entries.length route.output
  let checkNext := checkedSequenceNext (.nested 0) (fun (_ : Unit) => publish >>= fun value => pure (.ok value)) site.reply
  let canonNext := fun (_ : Unit) => publish >>= site.referenceReply
  let terminal := CollectionSegmentReplies profile ready base bindings older site leftStart rightStart
    (MapReturnStop destination site.inst .string element entries route.output basePtr site.referenceReply) offset
  if present : index < entries.length then
    let ptr := basePtr + index * stride
    let mode := CanonicalTree.EntryMode.forOutput destination.width (.map .string element) route.output
    let rest := entries.drop (index + 1)
    let checkTail := fun verdict : Except Stored.Endpoints.RecordLower.Issue Unit => (match verdict with
      | .error issue => pure (.error issue)
      | .ok () => OwnedMemory.Claims.Record.Effects.elements recordClaims Limits.spec Quirks.none cx destination.width
          rest stride (ptr + stride) (index + 1)) >>= checkNext
    let canonTail := fun (_ : Unit) => CanonicalTree.elements Limits.spec Quirks.none cx destination.width
      rest mode stride (ptr + stride) >>= canonNext
    ∃ (key : LinkedCallback.StringField) (value : Field), entries[index] = .aggregate type [key.field, value] ∧
      let keyArea := layout destination.width key.field.type
      let keyPtr := alignTo ptr keyArea.alignment
      let afterKey := keyPtr + keyArea.size
      let pending := mapValueProgram destination site.inst mode value afterKey canonTail
      let valuePtr := alignTo afterKey (layout destination.width value.type).alignment
      let report := fun verdict : Except Stored.Endpoints.RecordLower.Issue Unit => checkTail (verdict.mapError (.nested index))
      let checked := fun verdict : Except Stored.Endpoints.RecordLower.Issue Unit => (match verdict with
        | .error issue => pure (.error issue)
        | .ok () => OwnedMemory.Claims.Record.Effects.field recordClaims Limits.spec Quirks.none cx destination.width
            value 1 (.memory valuePtr)) >>= report
      let plan := storePlanFor Quirks.none destination.encoding destination.width key.value
      let checkString := fun addr => stringPlanTail cx destination.width (.memory keyPtr) plan addr >>= fun result => checked (.ok result)
      let canonString := fun addr => stringPlanTail cx destination.width (.memory keyPtr) plan addr >>= fun _ => pending
      let checkBody := { left with ctl := check.control (runStoreSteps cx 0 plan.steps >>= checkString) }
      let canonBody := { right with ctl := canon.control (runStoreSteps cx 0 plan.steps >>= canonString) }
      ComparedSlots profile ready base bindings left right [] checkBody canonBody ∧
      LiveStringPaths profile ready base bindings older cx checkString canonString leftStart rightStart
        (fun _ lhs rhs cursor _ observations => terminal ∨
          ∃ nextLeft nextRight nextCanon suffix,
            ComparedSlots profile ready base bindings lhs rhs suffix nextLeft nextRight ∧
            LinkedStringMapPaths profile ready base bindings older site element entries (index + 1) basePtr
              leftStart rightStart nextLeft nextRight cursor nextCanon (observations ++ suffix) offset)
        plan.steps.length checkBody canonBody check canon seen offset
  else terminal
termination_by entries.length - index

/-- The actual paths after a marked outer allocator return, for either public give.
Before entry, refusal retains the outer frame offset. After entry, each finite
allocator prefix is tracked from the return state and terminal replies use the
original caller. -/
def LinkedStringMapReturnPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (element : Stored.TypeOf) (entries : List Stored.Endpoints.RecordLower.Field)
    (pointer : Nat) (checked canonical : Config (core3 grow) (HostState sig))
    (check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) : Prop :=
  CollectionSegmentReplies profile ready base bindings older site checked canonical
    (MapReturnStop site.destination site.inst .string element entries route.output pointer site.referenceReply) ∨
  ∃ left right canon seen, ComparedSlots profile ready base bindings checked canonical seen left right 1 ∧
    LinkedStringMapPaths profile ready base bindings older site element entries 0 pointer checked canonical left right
      check canon seen 1

/-- From the real linked call on the canonical side, compare every classified
outer allocator prefix after checked admission. A natural-pointer return
of the installed occurrence feeds the original replies proof. -/
def LinkedStringMapDispatch (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (element : Stored.TypeOf) (entries : List Stored.Endpoints.RecordLower.Field)
    (incoming : Config (core3 grow) (HostState sig)) : Prop :=
  open Stored.Endpoints.RecordLower ABI PayloadPrefix in
  let area := layout site.destination.width (.record (mapEntryFields .string element))
  let mode := CanonicalTree.EntryMode.forOutput site.destination.width (.map .string element) route.output
  let first := checkedCollectionResume site.destination site.inst entries area 0 route.output site.reply
  let second := canonicalCollectionResume site.destination site.inst entries area route.output site.referenceReply mode
  let leftEntry := collectionEntry site.destination site.inst area entries.length (specDispatch ready base) site.checked site.cursor first
  let canonical := specDispatch ready (LiveDispatch.host bindings base)
  ∃ leading entered peer, visible leading = [] ∧ Steps profile ready canonical incoming leading entered ∧
    entered.host = incoming.host ∧
    let rightEntry := collectionEntry site.destination site.inst area entries.length canonical entered peer second
    ∀ {seen checked}, ClosedCallbackPrefix bindings profile ready base
        (fun resume => (∃ paired, older resume paired) ∨ resume = first) leftEntry seen checked →
      ∃ checkLabels canonLabels reached mark,
        AllocatorMark profile ready base bindings older leftEntry rightEntry checkLabels canonLabels checked reached mark ∧
        HostFrame.Related.Paired (ReturnFrame.Extend older first second) checked reached ∧
        ComparedPaths profile ready base bindings site.checked incoming seen checked reached ∧
        ∀ pointer check, mark = some (.active 0 0) →
          checked.ctl = { check with frames := .prog first :: check.frames }.control (.pure (.nat pointer)) →
          LinkedStringMapReturnPaths profile ready base bindings older site element entries pointer checked reached check

abbrev CollectionReplies (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (checked canonical : Config (core3 grow) (HostState sig))
    (childEntry : Session grow sig (Ret (core3 grow))) : Prop :=
  CollectionSegmentReplies profile ready base bindings older site checked canonical (· = childEntry)

/-- Stops before the recursive body. A checked preflight refusal resumes its
caller; a bad placement traps the checked machine. Neither executes the
canonical body, whose memory placement is a precondition. -/
inductive RootStop (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route) :
    Trace grow sig → Config (core3 grow) (HostState sig) → Prop where
  | refused (issue : Stored.Endpoints.RecordLower.Issue) {labels}
      (silent : PayloadPrefix.visible labels = [])
      (edge : Transition profile ready base site.start (.give route (.refused issue)) labels (site.refusedReply issue)) :
      RootStop profile ready base site labels (site.refusedReply issue)
  | placementTrap (reason : TrapReason) (count : Nat)
      (edge : Transition profile ready base site.start (.give route (.placementTrap reason))
        (List.replicate count .tau ++ [.trap reason]) (StepDefs.trapCfg site.checked)) :
      RootStop profile ready base site (List.replicate count .tau ++ [.trap reason]) (StepDefs.trapCfg site.checked)

/-- A finite decomposition of a checked run into scheduler segments and
compared gives. The canonical body of a give is itself a plan, so callouts
under a parked allocator can be compared before following the outer suffix.
Local body evidence names the actual replies or stop; it does not supply a
run at the replacement host or the older paired frames. -/
inductive NestedPlan (bindings : List (Binding sig)) (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) :
    Config (core3 grow) (HostState sig) → Trace grow sig → Config (core3 grow) (HostState sig) → Prop where
  | segment {start labels finish}
      (run : Steps profile ready (specDispatch ready base) start labels finish) :
      NestedPlan bindings profile ready base start labels finish
  | localSegment {start labels finish}
      (run : PayloadPrefix.LocalSteps profile ready (specDispatch ready base) start labels finish) :
      NestedPlan bindings profile ready base start labels finish
  | closedGive {start count} (callout : LinkedCallback.ClosedGive bindings start)
      (run : Steps profile ready (specDispatch ready base) start (List.replicate count .tau) callout.resume) :
      NestedPlan bindings profile ready base start (List.replicate count .tau) callout.resume
  | syncReady {start task inst thread frames rest}
      (focused : start.ctl = ⟨thread, .prog (.op .hostGet (fun current =>
        syncLiftCandidates task (start.store.instCandidates (ready current) inst))), frames⟩ :: rest)
      (agrees : LinkedCallback.ReadyAgreement ready start inst) :
      NestedPlan bindings profile ready base start [.tau] { start with ctl := ⟨thread,
        .prog (syncLiftCandidates task (start.store.instCandidates (ready start.host) inst)), frames⟩ :: rest }
  | commit {start target index} (resolve : ComponentCall.Delivery.LinkedResolution start target index) :
      NestedPlan bindings profile ready base start (List.replicate 17 .tau) resolve.committed
  | poll {start target index result suffix} (poll : ComponentCall.Delivery.ParkedPoll start target profile)
      (pending : ComponentCall.Delivery.PendingAt start.store target index)
      (branch : BufferBranch start.store poll.memory (flatNat poll.out) result suffix) :
      NestedPlan bindings profile ready base start (pollLabels poll ++ suffix)
        (result.finish (pollReply poll index) { start with store := StepDefs.lockdownSt poll.delivered, ctl := [] })
  | waitBlock {start} (wait : ComponentCall.Delivery.ParkedWait start) (empty : start.store.wsetHasEvent wait.ws = false) :
      NestedPlan bindings profile ready base start (List.replicate 13 .tau) wait.blocked
  | waitReady {start} (wait : ComponentCall.Delivery.ParkedWait start) (available : start.store.wsetHasEvent wait.ws = true)
      (early : Bool) (allowed : Allowed profile (.earlyReturn .waitableSetWait) early) :
      NestedPlan bindings profile ready base start (ComponentCall.Delivery.ParkedWait.readyLabels early)
        (if early then wait.early else wait.blocked)
  | waitResume {initial start} {wait : ComponentCall.Delivery.ParkedWait initial}
      (resume : ComponentCall.Delivery.WaitResume wait start) (saved : start.cont? wait.thread = some wait.saved) :
      NestedPlan bindings profile ready base start (List.replicate 4 .tau) resume.reached
  | waitTake {initial start target index result suffix} {wait : ComponentCall.Delivery.ParkedWait initial}
      (delivery : ComponentCall.Delivery.WaitDelivery wait start profile target)
      (focused : start.ctl = ⟨some wait.thread, .prog wait.takeEvent, .core wait.core wait.next :: wait.segments⟩ :: start.ctl.drop 1)
      (pending : ComponentCall.Delivery.PendingAt start.store target index)
      (branch : BufferBranch delivery.delivered wait.memory (flatNat wait.out) result suffix) :
      NestedPlan bindings profile ready base start (delivery.labels ++ suffix)
        (result.finish (delivery.resumed index) { start with store := StepDefs.lockdownSt delivery.delivered, ctl := [] })
  | cancelReturned {start target index} (cancel : ComponentCall.Delivery.ParkedCancel start target)
      (pending : ComponentCall.Delivery.PendingAt start.store target index)
      (available : ComponentCall.Delivery.CancelAvailable start.store target) :
      NestedPlan bindings profile ready base start (List.replicate 15 .tau) cancel.resumed
  | cancelRequest {start target} (cancel : ComponentCall.Delivery.ParkedCancel start target) (record : Subtask)
      (live : start.store.subtask? target = some record) (unresolved : record.state.resolved = false)
      (notDelivered : record.lenders.isSome = true) (notRequested : record.cancellationRequested = false)
      (notJoined : record.common.wset = none) :
      NestedPlan bindings profile ready base start (List.replicate 14 .tau) (cancel.callbackEntry record ready base)
  | cancelReentry {start target callee} {cancel : ComponentCall.Delivery.ParkedCancel start target}
      (request : ComponentCall.Delivery.TaskCancelAdmission cancel) (mode : ComponentCall.Delivery.TaskCancelReentry request ready)
      (saved : start.cont? request.implicitThread = some callee) :
      NestedPlan bindings profile ready base start (List.replicate request.reentrySteps .tau) (request.reentered callee)
  | cancelCallbackDone {start target} {cancel : ComponentCall.Delivery.ParkedCancel start target}
      (request : ComponentCall.Delivery.StartedCancel cancel) :
      NestedPlan bindings profile ready base start (List.replicate 20 .tau) request.callbackReturned
  | cancelPark {initial start target} {cancel : ComponentCall.Delivery.ParkedCancel initial target}
      (wait : ComponentCall.Delivery.SyncCancelWait cancel start) :
      NestedPlan bindings profile ready base start (List.replicate 5 .tau) wait.blocked
  | cancelResume {initial start target} {cancel : ComponentCall.Delivery.ParkedCancel initial target}
      (resume : ComponentCall.Delivery.SyncCancelResume cancel start) (saved : start.cont? cancel.thread = some cancel.saved) :
      NestedPlan bindings profile ready base start (List.replicate 3 .tau) resume.reached
  | cancelFinish {initial start target rest} (cancel : ComponentCall.Delivery.ParkedCancel initial target) (record : Subtask)
      (focused : start.ctl = ⟨some cancel.thread, .prog (ComponentCall.Delivery.ParkedCancel.finish target),
        .core cancel.core cancel.next :: cancel.segments⟩ :: rest)
      (live : start.store.subtask? target = some record) (resolved : record.state.resolved = true)
      (pending : record.common.pending = some (.subtask target)) :
      NestedPlan bindings profile ready base start (List.replicate 6 .tau) (cancel.finishReply start record.state rest)
  | sequence {start middle finish leading trailing}
      (front : NestedPlan bindings profile ready base start leading middle)
      (back : NestedPlan bindings profile ready base middle trailing finish) :
      NestedPlan bindings profile ready base start (leading ++ trailing) finish
  | rootStop {route} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings) {labels checked}
      (stop : RootStop profile ready base site labels checked) :
      NestedPlan bindings profile ready base site.start labels checked
  | compilerStop {start route issue count} {request : CoreGiveRequest bindings start}
      (selection : request.Selected route) (refused : selection.preflight = .error issue)
      (checked : Steps profile ready (specDispatch ready base) start (List.replicate count .tau) (selection.compilerRefused issue)) :
      NestedPlan bindings profile ready base start (List.replicate count .tau) (selection.compilerRefused issue)
  | give {route} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
      {entryLabels checkLabels referenceLabels reached reference checked baseline}
      (entry : Transition profile ready base site.start (.give route .entered) entryLabels site.checked)
      (checkedBody : Steps profile ready (specDispatch ready base) site.checked checkLabels reached)
      (body : NestedPlan bindings profile ready base (site.reference site.referenceReply) (referenceLabels ++ [.tau]) baseline)
      (value : route.output.Result)
      (replies : LinkedCallback.MemorySequence.GiveReplies site value profile ready reached reference checked baseline)
      (seen : PayloadPrefix.visible checkLabels = PayloadPrefix.visible referenceLabels) :
      NestedPlan bindings profile ready base site.start (entryLabels ++ checkLabels ++ [.tau, .tau, .tau]) checked
  | stop {route} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
      {entryLabels checkLabels referenceLabels reached reference phase check}
      (entry : Transition profile ready base site.start (.give route .entered) entryLabels site.checked)
      (checkedBody : Steps profile ready (specDispatch ready base) site.checked checkLabels reached)
      (body : NestedPlan bindings profile ready base (site.reference site.referenceReply) referenceLabels reference)
      (stop : GiveStop site check phase referenceLabels reached reference)
      (store : reached.store = reference.store)
      (seen : PayloadPrefix.visible checkLabels = PayloadPrefix.visible referenceLabels) :
      NestedPlan bindings profile ready base site.start (entryLabels ++ checkLabels) reached

/-- An exact callback trace reaches a dispatch lookup not covered by the
classified window. The prefix retains its specialized edges, and the
source suffix is retained but not replayed. A window ending at a lifted
install does not assert that the subsequent arena read will disagree. -/
def CallbackOverlayCut (bindings : List (Binding sig)) (profile : ProfileKind) (ready : HostReady (HostState sig))
    (callees : List (ComponentCall.Callee sig)) (start : Config (core3 grow) (HostState sig))
    (labels : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ middle after leading window suffix, labels = leading ++ window ++ suffix ∧
    NestedPlan bindings profile ready (ComponentCall.hostWithComponent bindings callees) start leading middle ∧
    Dispatch.LookupCut profile ready bindings callees middle window after ∧
    Steps profile ready (Dispatch.coreOnly ready bindings) after suffix finish

/-- At a fully classified window, retain both the exact dispatcher comparison
and the specialized edges needed to replay against a paired host. -/
def CallbackOverlayPlan (bindings : List (Binding sig)) (profile : ProfileKind) (ready : HostReady (HostState sig))
    (callees : List (ComponentCall.Callee sig)) (start : Config (core3 grow) (HostState sig))
    (labels : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  Dispatch.Compatible profile ready bindings callees start labels finish ∧
    NestedPlan bindings profile ready (ComponentCall.hostWithComponent bindings callees) start labels finish

/-- The comparison at an actual successful return. If a dispatcher window
cannot be transported, the checked/canonical replies from the narrower
comparison remain evidence, not a claim of a live canonical reply. -/
def LinkedGiveExit (bindings : List (Binding sig)) (profile : ProfileKind) (ready : HostReady (HostState sig))
    (callees : List (ComponentCall.Callee sig)) {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (entryLabels : Trace grow sig) (value : route.output.Result)
    (reached reference : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ checkLabels canonLabels checked baseline,
    LinkedCallback.MemorySequence.GiveReplies site value profile ready reached reference checked baseline ∧
    (NestedPlan bindings profile ready (ComponentCall.hostWithComponent bindings callees) site.start
        (entryLabels ++ checkLabels ++ [.tau, .tau, .tau]) checked ∨
      CallbackOverlayCut bindings profile ready callees site.checked checkLabels reached ∨
      CallbackOverlayCut bindings profile ready callees (site.reference site.referenceReply) canonLabels reference)

/-- Reasons to stop at an actual live configuration. A local checked stop
has a matched store and observed trace, but does not rejoin (including when
the plan has a later checked-only suffix). Unselected roots are not assumed
to retain their previous tree across earlier compared episodes. -/
inductive NestedCut (bindings : List (Binding sig)) (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) :
    Config (core3 grow) (HostState sig) → Prop where
  | request {before incoming label after}
      (paired : HostFrame.Related.Paired older before incoming)
      (install : GiveInstall bindings (specDispatch ready base) before label after) :
      NestedCut bindings profile ready base older incoming
  | boundary {before incoming label after reached}
      (paired : HostFrame.Related.Paired older before incoming)
      (cut : HostFrame.Related.Boundary older before incoming label after reached)
      (checkedStep : Step profile ready (specDispatch ready base) before label after)
      (referenceStep : Step profile ready (specDispatch ready (host bindings base)) incoming label reached) :
      NestedCut bindings profile ready base older reached
  | unselected {route incoming} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
      (paired : HostFrame.Related.Paired older site.start incoming)
      (selection : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle ≠ some site.tree) :
      NestedCut bindings profile ready base older incoming
  | rootStop {route reached labels checked} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
      (stop : RootStop profile ready base site labels checked)
      (installed : HostFrame.Related.Paired older (site.reference site.referenceReply) reached) :
      NestedCut bindings profile ready base older reached
  | compilerLookup {start route incoming} {request : CoreGiveRequest bindings start}
      (selection : request.Selected route) (paired : HostFrame.Related.Paired older start incoming)
      (different : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted selection.handle ≠ some selection.tree) :
      NestedCut bindings profile ready base older incoming
  | compilerStop {start route issue reached count} {request : CoreGiveRequest bindings start}
      (selection : request.Selected route) (refused : selection.preflight = .error issue)
      (checked : Steps profile ready (specDispatch ready base) start (List.replicate count .tau) (selection.compilerRefused issue))
      (installed : HostFrame.Related.Paired older selection.canonicalPending reached) :
      NestedCut bindings profile ready base older reached
  | publication {start target index incoming} (resolve : ComponentCall.Delivery.LinkedResolution start target index)
      (paired : HostFrame.Related.Paired older start incoming)
      (different : ¬ ∃ writer, incoming.host.writer.register resolve.tree = .ok writer ∧
        writer.accepted.length = resolve.writer.accepted.length) :
      NestedCut bindings profile ready base older incoming
  | cancelReadiness {start target incoming} {cancel : ComponentCall.Delivery.ParkedCancel start target}
      (request : ComponentCall.Delivery.TaskCancelAdmission cancel) (mode : ComponentCall.Delivery.TaskCancelReentry request ready)
      (paired : HostFrame.Related.Paired older start incoming)
      (different : ¬ (request.callee.state = .started →
        request.markedStore.threadReady (ready incoming.host) request.implicitThread = true)) :
      NestedCut bindings profile ready base older incoming
  | stopped {route phase checkLabels referenceLabels liveLabels liveStart checked reference reached check}
      (site : PayloadRoot.Site grow sig route) (stop : GiveStop site check phase referenceLabels checked reference)
      (checkedBody : Steps profile ready (specDispatch ready base) site.checked checkLabels checked)
      (referenceBody : Steps profile ready (specDispatch ready (host bindings base)) liveStart liveLabels reached)
      (paired : HostFrame.Related.Paired older reference reached)
      (store : checked.store = reached.store)
      (seen : PayloadPrefix.visible checkLabels = PayloadPrefix.visible liveLabels) :
      NestedCut bindings profile ready base older reached

/-- Use the actual public entry cut before asking for a recursive body comparison. -/
inductive RootAdmission (bindings : List (Binding sig)) (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (body : Prop) : Prop where
  | stopped {labels checked} (stop : RootStop profile ready base site labels checked)
      (plan : NestedPlan bindings profile ready base site.start labels checked) :
      RootAdmission bindings profile ready base site body
  | entered {labels} (entry : Transition profile ready base site.start (.give route .entered) labels site.checked)
      (compared : body) : RootAdmission bindings profile ready base site body

/-- Entry and the recursive success continuation for either public ABI under
the worker's linked dispatcher. This supplies no callback return or progress. -/
def LinkedRootExit (bindings : List (Binding sig)) (profile : ProfileKind) (ready : HostReady (HostState sig))
    (callees : List (ComponentCall.Callee sig)) (route : GiveEffectRoute) : PayloadRoot.Site grow sig route → Prop :=
  match route with
  | .memory _ => fun site => ∃ depth,
    RootAdmission bindings profile ready (ComponentCall.hostWithComponent bindings callees) site
      (LinkedCallback.MemorySequence.ParkedMemoryBody site depth profile ready bindings (fun reached reference =>
        ∃ entryLabels, LinkedGiveExit bindings profile ready callees site entryLabels () reached reference))
  | .flat _ => fun site => ∃ flatDepth entryDepth,
    RootAdmission bindings profile ready (ComponentCall.hostWithComponent bindings callees) site
      (LinkedCallback.MemorySequence.ParkedFlatResult site flatDepth entryDepth profile ready bindings (fun value reached reference =>
        ∃ entryLabels, LinkedGiveExit bindings profile ready callees site entryLabels value reached reference))

/-- Compiler rejection has no emitter or canonical typed error. Success
supplies the real compiled site, whose later entry guards still execute. -/
inductive ReachedGiveAdmission (profile : ProfileKind) (ready : HostReady (HostState sig))
    (callees : List (ComponentCall.Callee sig)) {bindings : List (Binding sig)} {start : Config (core3 grow) (HostState sig)}
    {request : CoreGiveRequest bindings start} {route : GiveEffectRoute} (selection : request.Selected route) : Prop where
  | refused {issue count} (preflight : selection.preflight = .error issue)
      (checked : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees))
        start (List.replicate count .tau) (selection.compilerRefused issue))
  | compiled {tag payload arity children field plan} (preflight : selection.preflight = .ok (field, plan))
      (root : selection.tree = .tag ⟨tag, payload⟩ arity children)
      (linked : (selection.site tag payload arity children field).Linked bindings)
      (exit : LinkedRootExit bindings profile ready callees route (selection.site tag payload arity children field))

/-- At the real returned callers, replay a finite checked suffix under the
fixed dispatcher. Stop at reached nested installs, unequal reads, or
substituted returns. Without older substitutions, closed delivery can
continue from the actual scheduler records and the reached live journal. -/
structure RejoinedWorkerTail (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (ComponentCall.Callee sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (checked canonical : Config (core3 grow) (HostState sig)) : Prop where
  replay : ∀ {labels finish}, Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees))
    checked labels finish →
    PairedReplay bindings profile ready (ComponentCall.hostWithComponent bindings callees) older checked canonical labels finish
  delivery : (∀ first second, ¬ older first second) → ∀ {actions labels finish outgoing},
    JournalInterleaving profile ready (ComponentCall.hostWithComponent bindings callees)
      checked canonical.host actions labels finish outgoing →
    Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) checked labels finish ∧
    Steps profile ready (specDispatch ready (LiveDispatch.host bindings (ComponentCall.hostWithComponent bindings callees)))
      canonical labels (HostFrame.replace finish outgoing) ∧
    (canonical.host.writer.accepted = checked.host.writer.accepted → outgoing.writer.accepted = finish.host.writer.accepted)

/-- The all-location body for the route chosen by the reached live selector. -/
def RecursiveGiveOccurrencePaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (ComponentCall.Callee sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (incoming : Config (core3 grow) (HostState sig)) : (route : GiveEffectRoute) → PayloadRoot.Site grow sig route → Prop
  | .memory _, site => LinkedMemoryOccurrenceBody profile ready (ComponentCall.hostWithComponent bindings callees) bindings older site incoming
  | .flat _, site => LinkedFlatOccurrenceBody profile ready (ComponentCall.hostWithComponent bindings callees) bindings older site incoming

/-- The recursive body and caller paths for whichever ABI the live selector
chose. A reached reply carries its next worker comparison, but neither a
reply nor an allocator return is required. -/
def RecursiveGivePaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (ComponentCall.Callee sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (incoming : Config (core3 grow) (HostState sig)) : (route : GiveEffectRoute) → PayloadRoot.Site grow sig route → Prop
  | .memory _, site => LinkedMemoryRejoinPaths profile ready (ComponentCall.hostWithComponent bindings callees) bindings older site incoming
    (RejoinedWorkerTail profile ready bindings callees older)
  | .flat _, site => LinkedFlatAggregateRejoinPaths profile ready (ComponentCall.hostWithComponent bindings callees) bindings older site incoming
    (RejoinedWorkerTail profile ready bindings callees older)

/-- The canonical root has installed its real body but has not executed it.
Record the original occurrence trail at this cut; the checked side can
already have issued a refusal or entered lockdown. -/
def PendingRecursiveRoot (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (ComponentCall.Callee sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (incoming : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ leading entered, PayloadPrefix.visible leading = [] ∧
    (∀ place, ReturnFrame.Occurrence.Prefix profile ready
      (specDispatch ready (host bindings (ComponentCall.hostWithComponent bindings callees)))
      incoming place leading entered
      (((ReturnFrame.Occurrence.Edit.push (.core site.core site.resume)).follow place).getD place)) ∧
    HostFrame.Related.Paired older (site.reference site.referenceReply) entered ∧ entered.host = incoming.host

/-- The checked side records the typed reply and pops its Core caller. The
canonical side stays at the exact already reached child entry, so its older
occurrences keep their pre-reply positions. -/
def PublicCollectionRefusalOccurrences (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (incoming checked canonical : Config (core3 grow) (HostState sig)) (seen : Trace grow sig)
    (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (type element : Stored.TypeOf) (entries : List Stored.Endpoints.RecordLower.Field) (pointer : Nat) : Prop :=
  open Stored.Endpoints.RecordLower ABI PayloadPrefix ReturnFrame.Occurrence in
  let area := layout site.destination.width element
  let mode := CanonicalTree.EntryMode.forOutput site.destination.width type route.output
  ∀ bytes, (core3 grow).memSize? checked.store.core site.destination.memory = some bytes →
    pointer = alignTo pointer area.alignment → pointer + entries.length * area.size ≤ bytes →
    ∀ issue, OwnedMemory.Claims.Record.prepare checked.store checked.host.writer (Field.listObjects entries) = .error issue →
      let reply := route.reply site.destination site.start.host.nextTicket (.error (LinkedCallback.CollectionVisit.afterAllocation 0 issue))
      let child := canonicalCollectionTail site.destination site.inst entries area route.output pointer mode >>= site.referenceReply
      ∃ (canon : Cursor (E := core3 grow) (HostState sig)) (segments : List (Seg (core3 grow) (HostState sig)))
          (checkLabels canonLabels : Trace grow sig),
        let resumed := (core3 grow).resume checked.store.core site.core (.values reply.2)
        let left := { checked with host := checked.host.record reply.1, ctl := ⟨cursor.thread, .core resumed site.resume, segments⟩ :: cursor.rest }
        let right := { canonical with ctl := canon.control child }
        visible checkLabels = seen ∧ visible canonLabels = seen ∧ left.store = right.store ∧
        ∀ mark : Option Location, ∃ atReply,
          Trail profile ready (specDispatch ready base) site.start mark checkLabels left
            (atReply.bind (Edit.pop : Edit (core3 grow) (HostState sig)).follow) ∧
          Trail profile ready (specDispatch ready (host bindings base)) incoming mark canonLabels right atReply

/-- From the original public request to the actual installed collection
allocator, then to the first range/recheck outcome if that occurrence returns.
The initial checked and reference programs are the real public entries. -/
def PublicCollectionOccurrences (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (ComponentCall.Callee sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (incoming : Config (core3 grow) (HostState sig)) (type element : Stored.TypeOf)
    (entries : List Stored.Endpoints.RecordLower.Field) : Prop :=
  let base := ComponentCall.hostWithComponent bindings callees
  let area := ABI.layout site.destination.width element
  let mode := Stored.Endpoints.RecordLower.CanonicalTree.EntryMode.forOutput site.destination.width type route.output
  let first := PayloadPrefix.checkedCollectionResume site.destination site.inst entries area 0 route.output site.reply
  let second := PayloadPrefix.canonicalCollectionResume site.destination site.inst entries area route.output site.referenceReply mode
  ∃ entered, ∃ canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig),
    ComparedOccurrencePaths profile ready base bindings site.start incoming [] site.checked entered ∧
    ∀ {seen finish}, ClosedCallbackPrefix bindings profile ready base (fun resume => (∃ peer, older resume peer) ∨ resume = first)
      (PayloadPrefix.collectionEntry site.destination site.inst area entries.length (specDispatch ready base) site.checked site.cursor first) seen finish →
      ∃ checkLabels canonLabels reached mark,
        AllocatorMark profile ready base bindings older
          (PayloadPrefix.collectionEntry site.destination site.inst area entries.length (specDispatch ready base) site.checked site.cursor first)
          (PayloadPrefix.collectionEntry site.destination site.inst area entries.length
            (specDispatch ready (host bindings base)) entered canon second) checkLabels canonLabels finish reached mark ∧
        ComparedOccurrencePaths profile ready base bindings site.start incoming seen finish reached ∧
        (∀ pointer (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)),
          mark = some (.active 0 0) →
          finish.ctl = { cursor with frames := .prog first :: cursor.frames }.control (.pure (.nat pointer)) →
          CollectionRangeOccurrences profile ready base bindings older site.start incoming finish reached seen
            cursor site.destination area entries.length pointer (Stored.Endpoints.RecordLower.Field.listObjects entries)
            (fun addr verdict => PayloadPrefix.checkedCollectionTail site.destination site.inst entries area 0 route.output addr verdict >>= site.reply)
            (fun addr => PayloadPrefix.canonicalCollectionTail site.destination site.inst entries area route.output addr mode >>= site.referenceReply) ∧
          PublicCollectionRefusalOccurrences profile ready base bindings site incoming finish reached seen cursor type element entries pointer)

/-- Classify the reached guard before recursive traversal starts. A
checked placement trap has its actual lockdown; it is not evidence that
the unexecuted canonical program has trapped at the same point. -/
inductive ReachedRecursiveRoot (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (ComponentCall.Callee sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (incoming : Config (core3 grow) (HostState sig))
    {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route) : Prop where
  | refused {issue labels} (silent : PayloadPrefix.visible labels = [])
      (checked : ∀ place, ReturnFrame.Occurrence.Trail profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees))
        site.start (some place) (labels ++ [.tau, .tau, .tau]) (site.refusedReply issue) (some place))
      (pending : PendingRecursiveRoot profile ready bindings callees older site incoming)
  | placementTrap {reason count}
      (verdict : PayloadPrefix.rootPlacement site.destination site.start.store (sig.payload site.tag) route.output = .error reason)
      (checked : site.EntryTrap profile ready (ComponentCall.hostWithComponent bindings callees)
        (List.replicate count .tau ++ [.trap reason]))
      (pending : PendingRecursiveRoot profile ready bindings callees older site incoming)
  | placed {labels} (silent : PayloadPrefix.visible labels = [])
      (verdict : PayloadPrefix.rootPlacement site.destination site.start.store (sig.payload site.tag) route.output = .ok ())
      (prepared : OwnedMemory.Claims.Record.prepare site.start.store site.start.host.writer site.field.objects = .ok ())
      (checked : site.EntryPrefix profile ready (ComponentCall.hostWithComponent bindings callees) labels site.checked)
      (pending : PendingRecursiveRoot profile ready bindings callees older site incoming)
      (body : RecursiveGivePaths profile ready bindings callees older incoming route site)

/-- Compare a give at its actual Core installation. A compiler refusal
can rejoin only the checked caller; the canonical body has not executed.
Successful compilation supplies the real checked entry and the recursive
paths from the live canonical caller, not from a fresh reference host. -/
inductive ReachedRecursiveGive (profile : ProfileKind) (ready : HostReady (HostState sig))
    (callees : List (ComponentCall.Callee sig)) {bindings : List (Binding sig)}
    {start : Config (core3 grow) (HostState sig)} {request : CoreGiveRequest bindings start}
    {route : GiveEffectRoute} (selection : request.Selected route)
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (incoming : Config (core3 grow) (HostState sig)) : Prop where
  | refused {issue count leading entered} (preflight : selection.preflight = .error issue)
      (checked : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees))
        start (List.replicate count .tau) (selection.compilerRefused issue))
      (silent : PayloadPrefix.visible leading = [])
      (canonical : Steps profile ready (specDispatch ready (host bindings (ComponentCall.hostWithComponent bindings callees)))
        incoming leading entered)
      (pending : HostFrame.Related.Paired older selection.canonicalPending entered)
      (unchangedHost : entered.host = incoming.host)
      (occurrences : RequestExitOccurrences profile ready (ComponentCall.hostWithComponent bindings callees)
        bindings start incoming [] (selection.compilerRefused issue) entered)
  | compiled {tag payload arity children field plan} (preflight : selection.preflight = .ok (field, plan))
      (root : selection.tree = .tag ⟨tag, payload⟩ arity children)
      (linked : (selection.site tag payload arity children field).Linked bindings)
      (cut : ReachedRecursiveRoot profile ready bindings callees older incoming (selection.site tag payload arity children field))
      (occurrences : PayloadRoot.Cut (selection.site tag payload arity children field) profile ready bindings
        (RecursiveGiveOccurrencePaths profile ready bindings callees older incoming route (selection.site tag payload arity children field))
        (ComponentCall.hostWithComponent bindings callees))

/-- The comparison domain for a successfully compiled root. A compiler
refusal does not need the recursive body theorem at all. -/
def RecursiveGiveDomain {bindings : List (Binding sig)} {start : Config (core3 grow) (HostState sig)}
    {request : CoreGiveRequest bindings start} {route : GiveEffectRoute} (selection : request.Selected route) : Prop :=
  ∀ tag payload arity children field plan, selection.tree = .tag ⟨tag, payload⟩ arity children →
    selection.preflight = .ok (field, plan) → RecursiveCollectionType (sig.payload tag)

/-- Classify a reached Core give without choosing its route or body in
advance. The open lookup names the exact demanded handle. An ABI refusal
actually rejoins both callers, unlike a later checked compiler refusal. -/
inductive RecursiveRequestCut (profile : ProfileKind) (ready : HostReady (HostState sig))
    (callees : List (ComponentCall.Callee sig)) {bindings : List (Binding sig)}
    {start : Config (core3 grow) (HostState sig)} (request : CoreGiveRequest bindings start)
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (incoming : Config (core3 grow) (HostState sig)) : Prop where
  | lookup {handle} (demand : request.lookupDemand = some handle)
      (different : Stored.Endpoints.Core.childFromHistory start.host.writer.accepted handle ≠
        Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted handle)
  | trapped {reason leftCount rightCount}
      (caller : Plain.callerInstance start.store request.thread = .error (.trapped reason))
      (left : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees))
        start (List.replicate leftCount .tau ++ [.trap reason])
        (StepDefs.trapCfg { start with host := start.host.enter request.name request.kind request.args }))
      (right : Steps profile ready (specDispatch ready (host bindings (ComponentCall.hostWithComponent bindings callees)))
        incoming (List.replicate rightCount .tau ++ [.trap reason]) (StepDefs.trapCfg incoming))
  | refused {issue leftCount rightCount checked canonical}
      (verdict : Plain.runBody request.selectionProgram start.store start.host (some request.thread) =
        (start.store, start.host, .ok (.error issue)))
      (progress : 0 < leftCount)
      (left : ∀ place, ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees))
        start place (List.replicate leftCount .tau) checked place)
      (right : ∀ place, ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready (host bindings (ComponentCall.hostWithComponent bindings callees)))
        incoming place (List.replicate rightCount .tau) canonical place)
      (paired : HostFrame.Related.Paired older checked canonical)
      (checkedHost : checked.host = (start.host.enter request.name request.kind request.args).record (request.admissionReply issue).1)
      (canonicalHost : canonical.host = incoming.host)
      (tail : RejoinedWorkerTail profile ready bindings callees older checked canonical)
  | admitted {route} (selection : request.Selected route)
      (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted selection.handle = some selection.tree)
      (body : RecursiveGiveDomain selection → ReachedRecursiveGive profile ready callees selection older incoming)

/-- Both paths carry the same occurrence through the actual scheduler
edits. If the mark disappears, an equal segment cannot revive it. -/
def WorkerOccurrencePrefix (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (ComponentCall.Callee sig))
    (retained : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (start incoming : Config (core3 grow) (HostState sig)) (mark : Option ReturnFrame.Occurrence.Location)
    (labels : Trace grow sig) (checked canonical : Config (core3 grow) (HostState sig)) : Prop :=
  open ReturnFrame.Occurrence in
  let base := ComponentCall.hostWithComponent bindings callees
  ∃ reached, Trail profile ready (specDispatch ready base) start mark labels checked reached ∧
    Trail profile ready (specDispatch ready (host bindings base)) incoming mark labels canonical reached ∧
    Outside retained (segmentStorage checked) (segmentStorage canonical) reached ∧
    CoupledOccurrencePaths profile ready base bindings start incoming labels labels checked canonical

/-- The first reached cut in Core execution after a common reply. At a
give installation the canonical side follows the reached live selector;
the baseline tail witnesses only the checked execution. -/
inductive ClassifiedWorkerTail (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (ComponentCall.Callee sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (start incoming : Config (core3 grow) (HostState sig)) (labels : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig))
    (track : Trace grow sig → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) → Prop :=
      fun _ _ _ => True) : Prop where
  | complete {other}
      (live : Steps profile ready (specDispatch ready (host bindings (ComponentCall.hostWithComponent bindings callees)))
        incoming labels other)
      (paired : HostFrame.Related.Paired older finish other) (trail : track labels finish other)
  | request {leading label trailing beforeLeft beforeRight afterLeft}
      (split : labels = leading ++ label :: trailing)
      (checked : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) start leading beforeLeft)
      (live : Steps profile ready (specDispatch ready (host bindings (ComponentCall.hostWithComponent bindings callees)))
        incoming leading beforeRight)
      (paired : HostFrame.Related.Paired older beforeLeft beforeRight)
      (trail : track leading beforeLeft beforeRight)
      (install : GiveInstall bindings (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) beforeLeft label afterLeft)
      (cut : DirectGiveAt bindings beforeLeft ∨ ∃ request : CoreGiveRequest bindings beforeLeft,
        RecursiveRequestCut profile ready callees request older beforeRight)
      (tail : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) afterLeft trailing finish)
  | boundary {leading label trailing beforeLeft beforeRight afterLeft afterRight}
      (split : labels = leading ++ label :: trailing)
      (checked : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) start leading beforeLeft)
      (live : Steps profile ready (specDispatch ready (host bindings (ComponentCall.hostWithComponent bindings callees)))
        incoming leading beforeRight)
      (paired : HostFrame.Related.Paired older beforeLeft beforeRight)
      (trail : track leading beforeLeft beforeRight)
      (boundary : HostFrame.Related.Boundary older beforeLeft beforeRight label afterLeft afterRight)
      (checkedStep : Step profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) beforeLeft label afterLeft)
      (liveStep : Step profile ready (specDispatch ready (host bindings (ComponentCall.hostWithComponent bindings callees)))
        beforeRight label afterRight)
      (tail : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) afterLeft trailing finish)

/-- Continue from the actual resumed pair. A finite worker prefix can
finish, reach another give, or stop at a genuine open boundary. Older
origins follow the same scheduler steps on each side up to that cut. -/
def RequestWorkerTail (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (ComponentCall.Callee sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (request reference : Config (core3 grow) (HostState sig)) (seen : Trace grow sig)
    (checked canonical : Config (core3 grow) (HostState sig)) : Prop :=
  let base := ComponentCall.hostWithComponent bindings callees
  ∀ {labels finish}, Steps profile ready (specDispatch ready base) checked labels finish →
    ClassifiedWorkerTail profile ready bindings callees older checked canonical labels finish
      (fun added left right => RequestExitOccurrences profile ready base bindings request reference
        (seen ++ PayloadPrefix.visible added) left right)

/-- The residual run after replay through common ABI refusals. A short
refusal prefix has not reached its reply; the canonical machine is still
at the request. Admitted bodies and open hooks are separate next cuts. -/
inductive WorkerRefusalCut (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (ComponentCall.Callee sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (left right : Config (core3 grow) (HostState sig)) : Trace grow sig → Prop where
  | done : WorkerRefusalCut profile ready bindings callees older left right []
  | boundary {label remaining checked canonical}
      (cut : HostFrame.Related.Boundary older left right label checked canonical)
      (check : Step profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) left label checked)
      (live : Step profile ready (specDispatch ready (host bindings (ComponentCall.hostWithComponent bindings callees))) right label canonical) :
      WorkerRefusalCut profile ready bindings callees older left right (label :: remaining)
  | request {label remaining installed}
      (install : GiveInstall bindings (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) left label installed)
      (cut : DirectGiveAt bindings left ∨ ∃ request : CoreGiveRequest bindings left,
        RecursiveRequestCut profile ready callees request older right ∧
        ((∃ handle, request.lookupDemand = some handle ∧
            Stored.Endpoints.Core.childFromHistory left.host.writer.accepted handle ≠
            Stored.Endpoints.Core.childFromHistory right.host.writer.accepted handle) ∨
          (∃ reason, Plain.callerInstance left.store request.thread = .error (.trapped reason)) ∨
          (∃ route, Nonempty (request.Selected route)) ∨
          (∃ issue count replied, (label :: remaining).length < count ∧
            Plain.runBody request.selectionProgram left.store left.host (some request.thread) =
              (left.store, left.host, .ok (.error issue)) ∧
            Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) left
              (List.replicate count .tau) replied))) :
      WorkerRefusalCut profile ready bindings callees older left right (label :: remaining)

/-- Matched worker prefixes reach a paired cut and retain both original
request paths. The residual is still part of the actual checked run. -/
def WorkerRefusalRun (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (ComponentCall.Callee sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (request reference : Config (core3 grow) (HostState sig)) (seen : Trace grow sig)
    (checked canonical : Config (core3 grow) (HostState sig)) (labels : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig)) : Prop :=
  let base := ComponentCall.hostWithComponent bindings callees
  ∃ leading canonicalLeading trailing left right,
    labels = leading ++ trailing ∧
    Steps profile ready (specDispatch ready base) checked leading left ∧
    Steps profile ready (specDispatch ready (host bindings base)) canonical canonicalLeading right ∧
    PayloadPrefix.visible canonicalLeading = PayloadPrefix.visible leading ∧
    Steps profile ready (specDispatch ready base) left trailing finish ∧
    HostFrame.Related.Paired older left right ∧
    RequestExitOccurrences profile ready base bindings request reference (seen ++ PayloadPrefix.visible leading) left right ∧
    WorkerRefusalCut profile ready bindings callees older left right trailing

/-- Consume every reached common ABI refusal that finishes within the
supplied finite worker run. -/
def RequestWorkerRefusals (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (ComponentCall.Callee sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (request reference : Config (core3 grow) (HostState sig)) (seen : Trace grow sig)
    (checked canonical : Config (core3 grow) (HostState sig)) : Prop :=
  ∀ {labels finish}, Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) checked labels finish →
    WorkerRefusalRun profile ready bindings callees older request reference seen checked canonical labels finish

/-- A reached compiler rejection is not a common reply. The checked run
can end before that reply, or it can contain the exact checked handoff.
In the latter case canonical stops at its installed, unexecuted emitter. -/
def CompilerStopSuffix (profile : ProfileKind) (ready : HostReady (HostState sig))
    (callees : List (ComponentCall.Callee sig)) {bindings : List (Binding sig)}
    {start : Config (core3 grow) (HostState sig)} {request : CoreGiveRequest bindings start}
    {route : GiveEffectRoute} (selection : request.Selected route) (issue : Stored.Endpoints.RecordLower.Issue)
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (origin reference incoming : Config (core3 grow) (HostState sig))
    (seen labels : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  let base := ComponentCall.hostWithComponent bindings callees
  ∃ count,
    Steps profile ready (specDispatch ready base) start (List.replicate count .tau) (selection.compilerRefused issue) ∧
    (labels.length < count ∨ ∃ suffix leading entered,
      labels = List.replicate count .tau ++ suffix ∧
      Steps profile ready (specDispatch ready base) (selection.compilerRefused issue) suffix finish ∧
      Steps profile ready (specDispatch ready (host bindings base)) incoming leading entered ∧
      HostFrame.Related.Paired older selection.canonicalPending entered ∧ entered.host = incoming.host ∧
      RequestExitOccurrences profile ready base bindings origin reference seen (selection.compilerRefused issue) entered)

/-- Align a selected body execution with the given checked run. Departure
requires a different reached oracle answer or embedder action and leaves
two separate, actually derived residual paths. -/
inductive WorkerBodyAlignment (profile : ProfileKind) (ready : HostReady (HostState sig))
    (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (start body : Config (core3 grow) (HostState sig)) (bodyLabels actual : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig)) : Prop where
  | reached {suffix} (split : actual = bodyLabels ++ suffix) (tail : Steps profile ready dispatch body suffix finish)
  | inside {remaining} (split : bodyLabels = actual ++ remaining) (nonempty : remaining ≠ [])
      (remainingBody : Steps profile ready dispatch finish remaining body)
  | departure {leading expected taken rest suffix middle next actualNext}
      (bodySplit : bodyLabels = leading ++ expected :: rest) (actualSplit : actual = leading ++ taken :: suffix)
      (shared : Steps profile ready dispatch start leading middle) (different : expected ≠ taken)
      (branch : workerBranchLabel expected ∧ workerBranchLabel taken)
      (planned : Step profile ready dispatch middle expected next) (bodyTail : Steps profile ready dispatch next rest body)
      (actualStep : Step profile ready dispatch middle taken actualNext) (actualTail : Steps profile ready dispatch actualNext suffix finish)

/-- An aligned machine-local segment. The endpoint is reached only when the
original checked derivation executes the entire segment. -/
inductive LocalRunAlignment (profile : ProfileKind) (ready : HostReady (HostState sig))
    (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (target : Config (core3 grow) (HostState sig)) (planned actual : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig)) : Prop where
  | reached {residual} (split : actual = planned ++ residual)
      (tail : Steps profile ready dispatch target residual finish)
  | inside {remaining} (split : planned = actual ++ remaining) (nonempty : remaining ≠ [])
      (tail : Steps profile ready dispatch finish remaining target)

/-- Classify a finite run at its last compared field frontier. A prefix
inside a local leaf retains its original suffix without completing the leaf. -/
inductive ElementRunEnd (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig))
    (success : Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) → Prop)
    (refusal : Stored.Endpoints.RecordLower.Issue → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) → Prop)
    (left right : Config (core3 grow) (HostState sig)) (trailing : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop where
  | returned (reached : success left right)
  | refused (issue : Stored.Endpoints.RecordLower.Issue) (reached : refusal issue left right)
  | trapped (checked : left.ctl = []) (canonical : right.ctl = [])
  | inside {remaining target} (nonempty : remaining ≠ [])
      (tail : Steps profile ready (specDispatch ready base) finish remaining target)

def ElementRunSlice (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (success : Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) → Prop)
    (refusal : Stored.Endpoints.RecordLower.Issue → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) → Prop)
    (start incoming : Config (core3 grow) (HostState sig)) (actual : Trace grow sig) (finish : Config (core3 grow) (HostState sig))
    (writerFlow : Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) → Prop := fun _ _ => True) : Prop :=
  ∃ checked canonical trailing left right, actual = checked ++ trailing ∧
    PayloadPrefix.visible checked = PayloadPrefix.visible canonical ∧ left.store = right.store ∧
    OccurrenceTransport profile ready base bindings start incoming checked canonical left right ∧
    Steps profile ready (specDispatch ready base) left trailing finish ∧
    writerFlow left right ∧
    ElementRunEnd profile ready base success refusal left right trailing finish

/-- An allocated element sequence ending in the stated output continuations.
On refusal the checked body follows its error arm, while canonical remains
at the exact canonical suffix admitted by the sequence. -/
def AllocatedElementRun (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    {Result : Type} (checkNext : Except Stored.Endpoints.RecordLower.Issue Result → Session grow sig (Ret (core3 grow)))
    (canonNext : Result → Session grow sig (Ret (core3 grow))) (stopsAt : Session grow sig (Ret (core3 grow)) → Prop)
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (start incoming : Config (core3 grow) (HostState sig)) (actual : Trace grow sig) (finish : Config (core3 grow) (HostState sig))
    (writerFlow : Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) → Prop := fun _ _ => True) : Prop :=
  ElementRunSlice profile ready base bindings
    (fun left right => ∃ value, LinkedCallback.ChildFrameOver older left right check canon ∧
      left.ctl = check.control (checkNext (.ok value)) ∧ right.ctl = canon.control (canonNext value))
    (fun issue left right => left.ctl = check.control (checkNext (.error issue)) ∧
      ∃ stop, stopsAt stop ∧ right.ctl = canon.control stop) start incoming actual finish writerFlow

/-- Match the actual local descriptor program before exposing a successful
publication or a trap. A checked prefix inside the program cannot advance
the enclosing continuation. -/
def ValueCommitRun (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig)) (output : Stored.Lower.Output)
    (checkNext : LinkedCallback.MemorySequence.ValueCheckNext grow sig output)
    (canonNext : LinkedCallback.MemorySequence.ValueCanonNext grow sig output)
    (published : LinkedCallback.MemorySequence.ValueFinish grow sig output)
    (left right : Config (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (actual : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  open PayloadPrefix in
  ∃ (store : CStore (core3 grow)) (result : Except TrapReason output.Result) (labels : Trace grow sig),
    let lhs := localLeafEnd left left.host store check.thread check.frames check.rest (fun value => checkNext (.ok value)) result
    let rhs := localLeafEnd right right.host store canon.thread canon.frames canon.rest canonNext result
    OccurrenceTransport profile ready base bindings left right labels labels lhs rhs ∧
    PairedLeafSteps profile ready (specDispatch ready base) (specDispatch ready (LiveDispatch.host bindings base)) left right labels lhs rhs ∧
    LocalRunAlignment profile ready (specDispatch ready base) lhs labels actual finish ∧
    ∀ value, result = .ok value → published value lhs rhs check canon

/-- The suffix is the range program (including its marked pop), not a replay
of the checked child or error continuation. -/
def AlignedCollectionRange (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (leftEntry rightEntry checked canonical lhs rhs : Config (core3 grow) (HostState sig))
    (checkTrace canonTrace observed actual : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ leftTail rightTail,
    OccurrenceTransport profile ready base bindings leftEntry rightEntry
      (checkTrace ++ leftTail) (canonTrace ++ rightTail) lhs rhs ∧
    PayloadPrefix.visible leftTail = observed ∧ PayloadPrefix.visible rightTail = observed ∧ lhs.store = rhs.store ∧
    LocalRunAlignment profile ready (specDispatch ready base) lhs leftTail actual finish ∧
    PayloadPrefix.PairedLocalPath profile ready (specDispatch ready base) (specDispatch ready (LiveDispatch.host bindings base))
      checked canonical leftTail rightTail lhs rhs ∧
    VisitorWriterPath profile ready base bindings checked canonical leftTail rightTail lhs rhs

open Stored.OwnedMemory.Claims Stored.OwnedMemory.Claims.Record in
/-- A finite cut in the preceding range prefix has not read prepare. At
the executed read, compare its verdict against the actual pending raw
writer, without giving raw a prepare or consuming a child step. -/
def CollectionPrepareRun (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (checked canonical left right finish : Config (core3 grow) (HostState sig)) (actual : Trace grow sig)
    (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (plan : List Stored.Endpoints.RecordLower.Object)
    (next : Except Stored.Endpoints.RecordLower.Issue Unit → Session grow sig (Ret (core3 grow))) : Prop :=
  (∃ reader remaining, [.tau, .tau, .tau] = actual ++ remaining ∧
    CollectionPrepareSite profile ready base bindings checked canonical left right reader cursor plan next ∧
    Steps profile ready (specDispatch ready base) finish remaining reader) ∨
  ∃ reader residual, actual = [.tau, .tau, .tau, .tau] ++ residual ∧
    CollectionPrepareSite profile ready base bindings checked canonical left right reader cursor plan next ∧
    Steps profile ready (specDispatch ready base) left residual finish ∧
    ∀ pending, checked.host.writer.ClaimDiscrepancies canonical.host.writer pending →
      prepare reader.store reader.host.writer plan = prepare reader.store right.host.writer plan ∨
      ∃ probe, pending probe ∧ ReachedPrepareConflict reader.store reader.host.writer right.host.writer plan probe

/-- The concrete checked verdict chooses the reached continuation. A range
trap does not enter that continuation; a refusal leaves the peer at its
canonical child entry. -/
def CollectionRangeRun (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (leftEntry rightEntry checked canonical : Config (core3 grow) (HostState sig))
    (checkTrace canonTrace actual : Trace grow sig) (finish : Config (core3 grow) (HostState sig))
    (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (destination : RecordDestination) (area : ABI.Layout) (count pointer : Nat)
    (plan : List Stored.Endpoints.RecordLower.Object)
    (checkNext : Nat → Except Stored.Endpoints.RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Nat → Session grow sig (Ret (core3 grow))) : Prop :=
  let trap := fun reason => AlignedCollectionRange profile ready base bindings leftEntry rightEntry checked canonical
    (StepDefs.trapCfg checked) (StepDefs.trapCfg canonical) checkTrace canonTrace [.trap reason] actual finish
  ∃ bytes, (core3 grow).memAddrType? checked.store.core destination.memory = some destination.width ∧
    (core3 grow).memSize? checked.store.core destination.memory = some bytes ∧
    if pointer ≠ ABI.alignTo pointer area.alignment then trap .unalignedPointer
    else if pointer + count * area.size ≤ bytes then
      ∃ canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig),
        let verdict := OwnedMemory.Claims.Record.prepare checked.store checked.host.writer plan
        let lhs := { checked with ctl := cursor.control (checkNext pointer verdict) }
        let rhs := { canonical with ctl := canon.control (canonNext pointer) }
        LinkedCallback.ChildFrameOver older lhs rhs cursor canon ∧
        AlignedCollectionRange profile ready base bindings leftEntry rightEntry checked canonical lhs rhs checkTrace canonTrace [] actual finish ∧
        CollectionPrepareRun profile ready base bindings checked canonical lhs rhs finish actual cursor plan (checkNext pointer)
    else trap .outOfBounds

/-- Cut the collection field's original derivation at the install, callback,
or range frontier. The actual callback traces and peer are retained even
when no returning range path can be entered. -/
def CollectionRunSlice (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (destination : RecordDestination) (inst : InstId) (type element : Stored.TypeOf)
    (entries : List Stored.Endpoints.RecordLower.Field) (index : Nat) (output : Stored.Lower.Output)
    (checkNext : LinkedCallback.MemorySequence.ValueCheckNext grow sig output)
    (canonNext : LinkedCallback.MemorySequence.ValueCanonNext grow sig output)
    (start incoming : Config (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (actual : Trace grow sig) (finish : Config (core3 grow) (HostState sig))
    (before : Trace grow sig) (visit : Nat → Nat → TrailFinish grow sig) : Prop :=
  open PayloadPrefix Stored.Endpoints.RecordLower ReturnFrame.Occurrence in
  match OwnedMemory.Claims.Record.prepare start.store start.host.writer (Field.listObjects entries) with
  | .error issue =>
    let refusal := match issue with
      | .preflight reason => Issue.field index (.beforeAllocation reason)
      | reason => Issue.nested index reason
    let stopped := { start with ctl := check.control (checkNext (.error refusal)) }
    OccurrenceTransport profile ready base bindings start incoming [.tau, .tau] [] stopped incoming ∧
    LocalRunAlignment profile ready (specDispatch ready base) stopped [.tau, .tau] actual finish
  | .ok () =>
    let area := ABI.layout destination.width element
    let mode := CanonicalTree.EntryMode.forOutput destination.width type output
    let first := checkedCollectionResume destination inst entries area index output checkNext
    let second := canonicalCollectionResume destination inst entries area output canonNext mode
    let leftEntry := collectionEntry destination inst area entries.length (specDispatch ready base) start check first
    let rightEntry := collectionEntry destination inst area entries.length
      (specDispatch ready (LiveDispatch.host bindings base)) incoming canon second
    actual.length < 3 ∨ ∃ checked canonical trailing reached peer mark,
      let checkTrace := [.tau, .tau, .tau] ++ checked
      let canonTrace := [.tau, .tau] ++ canonical
      actual = checkTrace ++ trailing ∧
      PayloadPrefix.visible canonical = PayloadPrefix.visible checked ∧
      AllocatorMark profile ready base bindings older leftEntry rightEntry checked canonical reached peer mark ∧
      HostFrame.Related.Paired (ReturnFrame.Extend older first second) reached peer ∧
      OccurrenceTransport profile ready base bindings start incoming checkTrace canonTrace reached peer [mark] ∧
      VisitorWriterPath profile ready base bindings start incoming checkTrace canonTrace reached peer ∧
      Core3.Grows start.store.core reached.store.core ∧
      CallbackSliceEnd profile ready base bindings (ReturnFrame.Extend older first second) reached peer trailing finish ∧
      ((trailing = [] ∨ mark ≠ some (.active 0 0) ∨
        ¬ ∃ (pointer : Nat) (cursor : Cursor (E := core3 grow) (HostState sig)),
          reached.ctl = { cursor with frames := .prog first :: cursor.frames }.control (.pure (.nat pointer))) ∨
        ∃ (pointer : Nat) (cursor : Cursor (E := core3 grow) (HostState sig)) (residual : Trace grow sig),
          mark = some (.active 0 0) ∧ trailing = .tau :: residual ∧
          reached.ctl = { cursor with frames := .prog first :: cursor.frames }.control (.pure (.nat pointer)) ∧
          Steps profile ready (specDispatch ready base) { reached with ctl := cursor.control (first (.nat pointer)) } residual finish ∧
          CollectionRangeRun profile ready base bindings older start incoming reached peer checkTrace canonTrace trailing finish
            cursor destination area entries.length pointer (Field.listObjects entries)
            (fun addr verdict => checkedCollectionTail destination inst entries area index output addr verdict >>= checkNext)
            (fun addr => canonicalCollectionTail destination inst entries area output addr mode >>= canonNext) ∧
          (∀ bytes, (core3 grow).memSize? reached.store.core destination.memory = some bytes →
            pointer = ABI.alignTo pointer area.alignment → pointer + entries.length * area.size ≤ bytes →
            OwnedMemory.Claims.Record.prepare reached.store reached.host.writer (Field.listObjects entries) = .ok () →
            ∃ lhs rhs peerCursor, LinkedCallback.ChildFrameOver older lhs rhs cursor peerCursor ∧
              (core3 grow).memAddrType? lhs.store.core destination.memory = some destination.width ∧
              (core3 grow).memSize? lhs.store.core destination.memory = some bytes ∧
              Core3.Grows start.store.core lhs.store.core ∧
              lhs.ctl = cursor.control (checkedCollectionTail destination inst entries area index output pointer (.ok ()) >>= checkNext) ∧
              rhs.ctl = peerCursor.control (canonicalCollectionTail destination inst entries area output pointer mode >>= canonNext) ∧
              AlignedCollectionRange profile ready base bindings start incoming reached peer lhs rhs checkTrace canonTrace [] trailing finish ∧
              visit pointer bytes (before ++ PayloadPrefix.visible checked) lhs rhs cursor peerCursor))

/-- The observed return focus is not itself an executed pop. Only the
matched case advances both continuations and exposes an actual shorter
checked residual. A displaced or lost mark cannot authorize this pop. -/
def ActualMarkedPop (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (checkEntry canonEntry left right : Config (core3 grow) (HostState sig)) (checkTrace canonTrace : Trace grow sig)
    (mark : Option ReturnFrame.Occurrence.Location) (check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (first second : ReturnFrame.Continuation (core3 grow) (HostState sig)) (value : Ret (core3 grow))
    (actual : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  mark ≠ some (.active 0 0) ∨ (actual = [] ∧ finish = left) ∨
    ∃ (trailing : Trace grow sig) (canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)),
      let resumed := { left with ctl := check.control (first value) }
      let peer := { right with ctl := canon.control (second value) }
      mark = some (.active 0 0) ∧ actual = .tau :: trailing ∧ trailing.length < actual.length ∧
      Steps profile ready (specDispatch ready base) resumed trailing finish ∧
      Step profile ready (specDispatch ready (LiveDispatch.host bindings base)) right .tau peer ∧
      LinkedCallback.ChildFrameOver older left right check canon ∧
      CheckedSpendFlow left.host.writer right.host.writer resumed.host.writer peer.host.writer [] ∧
      CoupledOccurrencePaths profile ready base bindings checkEntry canonEntry (checkTrace ++ [.tau]) (canonTrace ++ [.tau]) resumed peer ∧
      ∀ {leftStart rightStart : Config (core3 grow) (HostState sig)} {leftLabels rightLabels : Trace grow sig},
        ∀ {enclosing : List (Option ReturnFrame.Occurrence.Location)},
        OccurrenceTransport profile ready base bindings leftStart rightStart leftLabels rightLabels left right
          (some (.active 0 0) :: enclosing) →
        OccurrenceTransport profile ready base bindings leftStart rightStart (leftLabels ++ [.tau]) (rightLabels ++ [.tau]) resumed peer
          (enclosing.map (fun place => place.bind (ReturnFrame.Occurrence.Edit.pop : ReturnFrame.Occurrence.Edit (core3 grow) (HostState sig)).follow))

/-- Compare the actual suffix of a reached cancellation-hook installation.
The installed occurrence can be lost or displaced; only its executed pop
enters the checked continuation, even if an equal hook frame is in focus. -/
def CancelHookCallbackSlice (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (resume : ReturnFrame.Continuation (core3 grow) (HostState sig))
    (checked canonical : Config (core3 grow) (HostState sig)) (actual : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig)) : Prop :=
  open ReturnFrame.Occurrence in
  (actual = [] ∧ finish = checked) ∨
    ∃ checkEntry canonEntry checkLabels canonLabels trailing reached peer mark,
      actual = .tau :: (checkLabels ++ trailing) ∧
      OccurrenceTransport profile ready base bindings checked canonical [.tau] [.tau] checkEntry canonEntry [some (.active 0 0)] ∧
      OccurrenceTransport profile ready base bindings checked canonical (.tau :: checkLabels) (.tau :: canonLabels) reached peer [mark] ∧
      VisitorWriterPath profile ready base bindings checked canonical (.tau :: checkLabels) (.tau :: canonLabels) reached peer ∧
      PayloadPrefix.visible checkLabels = PayloadPrefix.visible canonLabels ∧
      AllocatorMark profile ready base bindings older checkEntry canonEntry checkLabels canonLabels reached peer mark ∧
      CallbackSliceEnd profile ready base bindings (ReturnFrame.Extend older resume resume) reached peer trailing finish ∧
      ∀ value (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)),
        reached.ctl = { cursor with frames := .prog resume :: cursor.frames }.control (.pure value) →
        ActualMarkedPop profile ready base bindings older checkEntry canonEntry reached peer checkLabels canonLabels
          mark cursor resume resume value trailing finish

/-- Track the caller installed at the start of a component result path.
Resolution alone leaves the reply in focus. Only the checked residual's actual
pop of that occurrence can consume it; a missing or displaced mark cannot. -/
def ComponentMarkedReplyTail (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (start incoming reached peer : Config (core3 grow) (HostState sig)) (leading : Trace grow sig)
    (check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (first second : ReturnFrame.Continuation (core3 grow) (HostState sig))
    (suffix : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ mark, AllocatorMark profile ready base bindings older start incoming leading leading reached peer mark ∧
    (reached.ctl = check.control (.pure (.cancel .none)) →
      mark ≠ some (.active 0 0) ∨ ∃ after : PayloadPrefix.Cursor (E := core3 grow) (HostState sig),
        check = { after with frames := .prog first :: after.frames } ∧
        ActualMarkedPop profile ready base bindings older start incoming reached peer leading leading mark
          after first second (.cancel .none) suffix finish)

/-- Immediately after the admitted entry's final arena read, with this side's
own ticket and live child-selection result. -/
def componentPreflightAt (callee : ComponentCall.Callee sig) (caller : CallerId)
    (cx : LiftLowerContext (core3 grow)) (args : List FlatValue)
    (state : Config (core3 grow) (HostState sig)) (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) :
    Config (core3 grow) (HostState sig) :=
  { state with
    host := state.host.enter callee.name callee.coreType args
    ctl := cursor.control (ComponentCall.acceptCaller callee caller state.host.nextTicket state.host.writer.accepted state.store cx args) }

/-- A mismatch is at the actual registration-read continuations, not at an
unvalidated payload or an assumed disagreement of whole writer states. -/
inductive ComponentObservedAcceptance (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older wider : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (callee : ComponentCall.Callee sig) (caller : CallerId) (leftTicket rightTicket : Nat)
    (planned : Option (List (Stored.OwnedMemory.Tree sig)))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (first second : ReturnFrame.Continuation (core3 grow) (HostState sig))
    (start incoming reached peer : Config (core3 grow) (HostState sig)) (leading suffix : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig)) : Prop where
  | pending (exhausted : suffix = []) (paired : PairedComponentSite wider reached peer check canon)
      (writers : VisitorWriterPath profile ready base bindings start incoming leading leading reached peer)
  | trapped (checked : reached.ctl = []) (canonical : peer.ctl = [])
      (paired : HostFrame.Related.Paired wider reached peer)
      (writers : VisitorWriterPath profile ready base bindings start incoming leading leading reached peer)
  | registrationMismatch {tree : Stored.OwnedMemory.Tree sig}
      (mismatch : ReachedRegistrationMismatch profile ready base bindings reached peer check canon leftTicket rightTicket caller tree)
      (paired : PairedComponentSite wider reached peer check canon)
      (writerPath : VisitorWriterPath profile ready base bindings start incoming leading leading reached peer)
      (writers : reached.host.writer = start.host.writer ∧ peer.host.writer = incoming.host.writer)
      (entryDisagrees : ¬ start.host.writer.IndexedClaimsAgree incoming.host.writer)
  | refused
      (frontier : ComponentStoreFrontier (Result := Unit) wider check canon
        (fun _ => .pure (.cancel .none)) (fun _ => .pure (.cancel .none)) reached peer suffix True)
      (writers : VisitorWriterPath profile ready base bindings start incoming leading leading reached peer)
      (reply : ComponentMarkedReplyTail profile ready base bindings older start incoming reached peer leading
        check first second suffix finish)
  | accepted {tree handle}
      (frontier : ComponentAcceptedFrontier wider check canon tree handle reached peer suffix)
      (reply : ComponentMarkedReplyTail profile ready base bindings older start incoming reached peer leading
        check first second suffix finish)
      (writers : VisitorWriterPath profile ready base bindings start incoming leading leading reached peer)
      (writerFlow : ∀ pending,
        start.host.writer.ClaimDiscrepancies incoming.host.writer pending →
        reached.host.writer.ClaimDiscrepancies peer.host.writer pending)

/-- The classification after the admitted entry reaches child preflight.
Disagreement is on the demanded decision, not on the complete journals.
Each common decision consumes the checked residual from this exact site. -/
def ComponentPreflightTail (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older wider : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (callee : ComponentCall.Callee sig) (caller : CallerId) (leftTicket rightTicket : Nat)
    (leftPlan rightPlan : Except Scheduled.Issue (Option (List (Stored.OwnedMemory.Tree sig))))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (first second : ReturnFrame.Continuation (core3 grow) (HostState sig))
    (start incoming : Config (core3 grow) (HostState sig)) (labels : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig)) : Prop :=
  (leftPlan ≠ rightPlan ∧ start.host.writer.accepted ≠ incoming.host.writer.accepted) ∨
  ∃ plan, leftPlan = plan ∧ rightPlan = plan ∧
    match plan with
    | .error _ =>
      FramedComponentEarlyPrefix profile ready base bindings wider check canon start incoming labels finish 7 ∨
      ∃ leading suffix reached peer, labels = leading ++ suffix ∧
        OccurrenceTransport profile ready base bindings start incoming leading leading reached peer ∧
        VisitorWriterPath profile ready base bindings start incoming leading leading reached peer ∧
        Steps profile ready (specDispatch ready base) reached suffix finish ∧
        ComponentStoreFrontier (Result := Unit) wider check canon (fun _ => .pure (.cancel .none))
          (fun _ => .pure (.cancel .none)) reached peer suffix True ∧
        ComponentMarkedReplyTail profile ready base bindings older start incoming reached peer leading
          check first second suffix finish
    | .ok planned =>
      ∃ leading suffix reached peer, labels = leading ++ suffix ∧
        OccurrenceTransport profile ready base bindings start incoming leading leading reached peer ∧
        Steps profile ready (specDispatch ready base) reached suffix finish ∧
        ComponentObservedAcceptance profile ready base bindings older wider callee caller leftTicket rightTicket
          planned check canon first second start incoming reached peer leading suffix finish

/-- The finite body cut starts at the installed component invocation. The
seven-step entry is consumed only if present in the actual checked run. -/
def ComponentAdmissionCut (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older wider : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (callee : ComponentCall.Callee sig) (caller : CallerId) (cx : LiftLowerContext (core3 grow)) (args : List FlatValue)
    (check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (first second : ReturnFrame.Continuation (core3 grow) (HostState sig))
    (start incoming : Config (core3 grow) (HostState sig)) (labels : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig)) : Prop :=
  (∃ canon, FramedComponentEarlyPrefix profile ready base bindings wider check canon start incoming labels finish 7) ∨
  ∃ peerFrames peerRest suffix,
    let canon := { check with frames := peerFrames, rest := peerRest }
    let reached := componentPreflightAt callee caller cx args start check
    let peer := componentPreflightAt callee caller cx args incoming canon
    labels = List.replicate 7 .tau ++ suffix ∧
    OccurrenceTransport profile ready base bindings start incoming (List.replicate 7 .tau) (List.replicate 7 .tau) reached peer ∧
    VisitorWriterPath profile ready base bindings start incoming (List.replicate 7 .tau) (List.replicate 7 .tau) reached peer ∧
    Steps profile ready (specDispatch ready base) reached suffix finish ∧
    PairedComponentSite wider reached peer check canon ∧
    ComponentPreflightTail profile ready base bindings older wider callee caller start.host.nextTicket incoming.host.nextTicket
      (callee.childPreflight start.host.writer.accepted start.store cx args)
      (callee.childPreflight incoming.host.writer.accepted incoming.store cx args)
      check canon first second reached peer suffix finish

/-- The positive dispatch and admission branch, inspected at the actual call
site. Failure of this predicate is a frontier, not a synthetic runtime reply. -/
def ComponentHostAdmission (callees : List (ComponentCall.Callee sig)) (hostId : HostFuncId) (caller : CallerId)
    (active : ThreadId) (state : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ callee subtask cx args pos ft limits results entry task,
    callees.filter (·.hostId == hostId) = [callee] ∧
    ArenaField.callers.get? state.store caller = some (.lower subtask cx args pos ft limits results) ∧
    ArenaField.threads.get? state.store active = some entry ∧
    ArenaField.tasks.get? state.store entry.task = some task ∧ task.inst = callee.inst ∧
    callee.check state.store subtask cx args pos ft (limits, results) = .ok ()

/-- A failed link or admission follows the executed dispatcher through any
entry and diagnostic writes. An exhausted prefix may precede lockdown;
neither outcome claims an original caller pop. -/
def ComponentEntryFailure (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (ComponentCall.Callee sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (start incoming finish : Config (core3 grow) (HostState sig))
    (label : Label (core3 grow) (HostState sig)) (trailing : Trace grow sig) : Prop :=
  let base := ComponentCall.hostWithComponent (grow := grow) bindings callees
  ∃ leading suffix reached peer check canon,
    label = .tau ∧ trailing = leading ++ suffix ∧
    ∃ mark,
    OccurrenceTransport profile ready base bindings start incoming (.tau :: leading) (.tau :: leading) reached peer [mark] ∧
    VisitorWriterPath profile ready base bindings start incoming (.tau :: leading) (.tau :: leading) reached peer ∧
    Steps profile ready (specDispatch ready base) reached suffix finish ∧
    ((suffix = [] ∧ PairedComponentSite older reached peer check canon) ∨
      (reached.ctl = [] ∧ peer.ctl = [] ∧ HostFrame.Related.Paired older reached peer))

/-- Classify nominal linkage separately from the linked caller's admission.
Both failures carry their executed prefixes, not synthetic caller replies. -/
def ComponentInstallOutcome (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (ComponentCall.Callee sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (before incoming next finish : Config (core3 grow) (HostState sig)) (label : Label (core3 grow) (HostState sig))
    (trailing : Trace grow sig) : Prop :=
  ∀ active hostId caller resume frames rest,
    before.ctl = ⟨some active, .prog (.op (.call (.hostFunc hostId caller)) resume), frames⟩ :: rest →
    ((∃ callee, callees.filter (·.hostId == hostId) = [callee]) ∧
      ¬ ComponentHostAdmission callees hostId caller active before ∧
      ComponentEntryFailure profile ready bindings callees older before incoming finish label trailing) ∨
    ((¬ ∃ callee, callees.filter (·.hostId == hostId) = [callee]) ∧
      ComponentEntryFailure profile ready bindings callees older before incoming finish label trailing) ∨
    ∃ callee cx args peerFrames peerRest,
      let base := ComponentCall.hostWithComponent (grow := grow) bindings callees
      let peer := { incoming with ctl := ⟨some active, .prog (ComponentCall.invoke callee caller), .prog resume :: peerFrames⟩ :: peerRest }
      callees.filter (·.hostId == hostId) = [callee] ∧ label = .tau ∧
      OccurrenceTransport profile ready base bindings before incoming [.tau] [.tau] next peer [some (.active 0 0)] ∧
      ComponentAdmissionCut profile ready base bindings older older callee caller cx args
        ⟨some active, .prog resume :: frames, rest⟩ resume resume next peer trailing finish

/-- The worker prefix is paired until its first boundary. A component install
uses the boundary's exact checked step and suffix to classify the admitted body. -/
inductive ComponentWorkerCut (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (ComponentCall.Callee sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (start incoming : Config (core3 grow) (HostState sig)) (labels : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig)) : Prop where
  | complete {peer} (segment : ExecutedCallbackSegment profile ready (ComponentCall.hostWithComponent bindings callees)
      bindings older start incoming labels labels finish peer)
  | boundary {leading label trailing reached peer next}
      (split : labels = leading ++ label :: trailing)
      (segment : ExecutedCallbackSegment profile ready (ComponentCall.hostWithComponent bindings callees)
        bindings older start incoming leading leading reached peer)
      (kind : CallbackWorkerBoundary bindings ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees))
        (fun resume => ∃ other, older resume other) reached label next)
      (step : Step profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) reached label next)
      (tail : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) next trailing finish)
      (smaller : trailing.length < labels.length)
      (installed : ComponentInstallOutcome profile ready bindings callees older reached peer next finish label trailing)

/-- An actual finite mixed worker prefix under the fixed component dispatcher.
The residual retains its exact first step and tail; if it is a component
install, the live dispatch/admission classification is at that same site. -/
def MixedCallbackSlice (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (ComponentCall.Callee sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (start incoming : Config (core3 grow) (HostState sig)) (labels : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig)) : Prop :=
  let base := ComponentCall.hostWithComponent (grow := grow) bindings callees
  ∃ checked canonical trailing reached peer,
    labels = checked ++ trailing ∧
    ExecutedCallbackSegment profile ready base bindings older start incoming checked canonical reached peer ∧
    PairedWriterPaths profile ready base bindings start incoming checked canonical reached peer ∧
    CallbackSliceEnd profile ready base bindings older reached peer trailing finish ∧
    (∃ effects, WriterPath profile ready (specDispatch ready base) reached trailing finish effects) ∧
    ((trailing = [] ∧ finish = reached) ∨
      ∃ label rest next, trailing = label :: rest ∧
        Step profile ready (specDispatch ready base) reached label next ∧
        Steps profile ready (specDispatch ready base) next rest finish ∧
        ComponentInstallOutcome profile ready bindings callees older reached peer next finish label rest)

/-- Consume the actual post-pop worker run, when reached. A different resumed
program is an explicit boundary, not a replay or a runtime refusal. -/
def ComponentMarkedWorkerTail (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (start incoming reached peer : Config (core3 grow) (HostState sig)) (leading : Trace grow sig)
    (check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (first second : ReturnFrame.Continuation (core3 grow) (HostState sig))
    (suffix : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  open ReturnFrame.Occurrence in
  reached.ctl ≠ check.control (.pure (.cancel .none)) ∨
  (∃ mark, AllocatorMark profile ready base bindings older start incoming leading leading reached peer mark ∧
    mark ≠ some (.active 0 0)) ∨ (suffix = [] ∧ finish = reached) ∨
  ∃ (remaining : Trace grow sig) (after canonAfter : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)),
    let resumed := { reached with ctl := after.control (first (.cancel .none)) }
    let canon := { peer with ctl := canonAfter.control (second (.cancel .none)) }
    suffix = .tau :: remaining ∧ remaining.length < suffix.length ∧
    Steps profile ready (specDispatch ready base) resumed remaining finish ∧
    OccurrenceTransport profile ready base bindings start incoming (leading ++ [.tau]) (leading ++ [.tau]) resumed canon ∧
    (first (.cancel .none) ≠ second (.cancel .none) ∨
      ∃ checked canonical trailing worker workerPeer,
        remaining = checked ++ trailing ∧
        OccurrenceTransport profile ready base bindings start incoming
          ((leading ++ [.tau]) ++ checked) ((leading ++ [.tau]) ++ canonical) worker workerPeer ∧
        PayloadPrefix.visible canonical = PayloadPrefix.visible checked ∧
        CallbackSliceEnd profile ready base bindings older worker workerPeer trailing finish)

/-- Compare the checked run with the entry obtained from the real public
guards. A short run need not have taken the displayed refusal or trap. -/
inductive RecursiveRootEntryAlignment (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (ComponentCall.Callee sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (incoming : Config (core3 grow) (HostState sig)) {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (actual : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop where
  | refused {issue leading} (silent : PayloadPrefix.visible leading = [])
      (checked : ∀ place, ReturnFrame.Occurrence.Trail profile ready
        (specDispatch ready (ComponentCall.hostWithComponent bindings callees))
        site.start (some place) (leading ++ [.tau, .tau, .tau]) (site.refusedReply issue) (some place))
      (aligned : WorkerBodyAlignment profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees))
        site.start (site.refusedReply issue) (leading ++ [.tau, .tau, .tau]) actual finish)
  | placementTrap {reason count}
      (verdict : PayloadPrefix.rootPlacement site.destination site.start.store (sig.payload site.tag) route.output = .error reason)
      (checked : site.EntryTrap profile ready (ComponentCall.hostWithComponent bindings callees)
        (List.replicate count .tau ++ [.trap reason]))
      (aligned : WorkerBodyAlignment profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees))
        site.start (StepDefs.trapCfg site.checked) (List.replicate count .tau ++ [.trap reason]) actual finish)
  | placed {leading} (silent : PayloadPrefix.visible leading = [])
      (verdict : PayloadPrefix.rootPlacement site.destination site.start.store (sig.payload site.tag) route.output = .ok ())
      (prepared : OwnedMemory.Claims.Record.prepare site.start.store site.start.host.writer site.field.objects = .ok ())
      (checked : site.EntryPrefix profile ready (ComponentCall.hostWithComponent bindings callees) leading site.checked)
      (body : RecursiveGiveOccurrencePaths profile ready bindings callees older incoming route site)
      (aligned : WorkerBodyAlignment profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees))
        site.start site.checked leading actual finish)

/-- The actual checked residual of a selected give enters the compiler or
root cut only if the finite execution covers that entry. The canonical
pending state is not an error reply or a finished body. -/
inductive RecursiveGiveEntryAlignment (profile : ProfileKind) (ready : HostReady (HostState sig))
    (callees : List (ComponentCall.Callee sig)) {bindings : List (Binding sig)}
    {start : Config (core3 grow) (HostState sig)} {request : CoreGiveRequest bindings start}
    {route : GiveEffectRoute} (selection : request.Selected route)
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (incoming : Config (core3 grow) (HostState sig))
    (actual : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop where
  | compilerRefused {issue count entered} (preflight : selection.preflight = .error issue)
      (pending : HostFrame.Related.Paired older selection.canonicalPending entered)
      (occurrences : RequestExitOccurrences profile ready (ComponentCall.hostWithComponent bindings callees)
        bindings start incoming [] (selection.compilerRefused issue) entered)
      (aligned : WorkerBodyAlignment profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees))
        start (selection.compilerRefused issue) (List.replicate count .tau) actual finish)
  | compiled {tag payload arity children field plan} (preflight : selection.preflight = .ok (field, plan))
      (root : selection.tree = .tag ⟨tag, payload⟩ arity children)
      (linked : (selection.site tag payload arity children field).Linked bindings)
      (pending : PendingRecursiveRoot profile ready bindings callees older (selection.site tag payload arity children field) incoming)
      (aligned : RecursiveRootEntryAlignment profile ready bindings callees older incoming
        (selection.site tag payload arity children field) actual finish)

/-- Replay the closed part of the actual suffix after a common public reply.
A further give is classified at its reached pair, with the real checked
installation and tail. The suffix transports enclosing occurrences across
the closed steps, but does not replay any open action or protected pop. -/
def RejoinedCallbackReplay (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (ComponentCall.Callee sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (request reference checked canonical : Config (core3 grow) (HostState sig))
    (checkPrefix canonPrefix actual : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  let base := ComponentCall.hostWithComponent bindings callees
  let dispatch := specDispatch ready base
  ∃ leading remaining lhs rhs,
    actual = leading ++ remaining ∧ Steps profile ready dispatch checked leading lhs ∧
    Steps profile ready (specDispatch ready (host bindings base)) canonical leading rhs ∧
    HostFrame.Related.Paired older lhs rhs ∧
    CoupledOccurrencePaths profile ready base bindings request reference (checkPrefix ++ leading) (canonPrefix ++ leading) lhs rhs ∧
    OccurrenceTransport profile ready base bindings checked canonical leading leading lhs rhs ∧
    ((remaining = [] ∧ lhs = finish) ∨
      ∃ label tail next, remaining = label :: tail ∧ Step profile ready dispatch lhs label next ∧
        Steps profile ready dispatch next tail finish ∧
        CallbackWorkerBoundary bindings ready dispatch (fun resume => ∃ peer, older resume peer) lhs label next ∧
        (GiveInstall bindings dispatch lhs label next →
          DirectGiveAt bindings lhs ∨ ∃ req : CoreGiveRequest bindings lhs, RecursiveRequestCut profile ready callees req older rhs))

/-- Align the occurrence paths of a derived successful body with the finite
worker run. After an executed original pop, the suffix is taken from that
run. Writer classification of a selected request uses `ActualSelectedGive`. -/
def PublicTransportWorkerAlignment (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (ComponentCall.Callee sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (incoming left right : Config (core3 grow) (HostState sig))
    (checkEntry canonEntry seen actual : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  open ReturnFrame.Occurrence in
  let base := ComponentCall.hostWithComponent bindings callees
  let dispatch := specDispatch ready base
  ∃ (checkBody canonBody : Trace grow sig) (mark : Option Location),
    PayloadPrefix.visible checkBody = seen ∧ PayloadPrefix.visible canonBody = seen ∧
    OccurrenceTransport profile ready base bindings site.start incoming (checkEntry ++ checkBody) (canonEntry ++ canonBody)
      left right [mark] ∧
    WorkerBodyAlignment profile ready dispatch site.start left (checkEntry ++ checkBody) actual finish ∧
    ∀ tail, actual = (checkEntry ++ checkBody) ++ tail → Steps profile ready dispatch left tail finish →
      mark = some (.active 0 0) →
      CheckedCoreReplyPrefix profile ready dispatch left tail finish ∨ ∃ suffix checked canonical,
        tail = [.tau, .tau, .tau] ++ suffix ∧ suffix.length < actual.length ∧
        Steps profile ready dispatch checked suffix finish ∧ HostFrame.Related.Paired older checked canonical ∧
        OccurrenceTransport profile ready base bindings site.start incoming
          ((checkEntry ++ checkBody) ++ [.tau, .tau, .tau]) ((canonEntry ++ canonBody) ++ [.tau]) checked canonical ∧
        RejoinedWorkerTail profile ready bindings callees older checked canonical ∧
        RejoinedCallbackReplay profile ready bindings callees older site.start incoming checked canonical
          ((checkEntry ++ checkBody) ++ [.tau, .tau, .tau]) ((canonEntry ++ canonBody) ++ [.tau]) suffix finish ∧
        ∀ {retained enclosingLeft enclosingRight leftTrace rightTrace cursor},
          AllocatorMark profile ready base bindings retained enclosingLeft enclosingRight leftTrace rightTrace site.start incoming cursor →
          ∃ reached,
            AllocatorMark profile ready base bindings retained enclosingLeft enclosingRight
              (leftTrace ++ ((checkEntry ++ checkBody) ++ [.tau, .tau, .tau]))
              (rightTrace ++ ((canonEntry ++ canonBody) ++ [.tau])) checked canonical reached ∧
            ClassifiedWorkerTail profile ready bindings callees older checked canonical suffix finish
              (WorkerOccurrencePrefix profile ready bindings callees retained checked canonical reached)

/-- Match an actual checked run against a marked public body endpoint.
Only an executed reply pop supplies a worker suffix. A common return carries
the same older occurrence coordinates through both replies, including loss;
a typed reply does not authorize a canonical pop or suffix. -/
def PublicGiveWorkerAlignment (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (ComponentCall.Callee sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (entered left right : Config (core3 grow) (HostState sig))
    (verdict : Except Stored.Endpoints.RecordLower.Issue route.output.Result)
    (origin reference incoming : Config (core3 grow) (HostState sig))
    (entryLabels canonEntryLabels prior seen actual : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  open ReturnFrame.Occurrence in
  let base := ComponentCall.hostWithComponent bindings callees
  let dispatch := specDispatch ready base
  ∃ bodyLabels canonLabels mark,
    Trail profile ready dispatch site.checked (some (.active 0 0)) bodyLabels left mark ∧
    Trail profile ready (specDispatch ready (host bindings base)) entered (some (.active 0 0)) canonLabels right mark ∧
    RequestExitOccurrences profile ready base bindings origin reference (prior ++ seen) left right ∧
    WorkerBodyAlignment profile ready dispatch site.start left (entryLabels ++ bodyLabels) actual finish ∧
    ∀ tail, actual = (entryLabels ++ bodyLabels) ++ tail → Steps profile ready dispatch left tail finish →
      mark = some (.active 0 0) →
      tail.length < 3 ∨ ∃ suffix checked canonical,
        tail = [.tau, .tau, .tau] ++ suffix ∧ suffix.length < actual.length ∧
        Steps profile ready dispatch checked suffix finish ∧
        RequestExitOccurrences profile ready base bindings origin reference (prior ++ seen) checked canonical ∧
        match verdict with
        | .error _ => canonical = right
        | .ok _ => HostFrame.Related.Paired older checked canonical ∧
          CoupledOccurrencePaths profile ready base bindings site.start incoming
            ((entryLabels ++ bodyLabels) ++ [.tau, .tau, .tau]) ((canonEntryLabels ++ canonLabels) ++ [.tau]) checked canonical ∧
          RejoinedCallbackReplay profile ready bindings callees older site.start incoming checked canonical
            ((entryLabels ++ bodyLabels) ++ [.tau, .tau, .tau]) ((canonEntryLabels ++ canonLabels) ++ [.tau]) suffix finish ∧
          WorkerRefusalRun profile ready bindings callees older origin reference (prior ++ seen) checked canonical suffix finish

/-- Use the checked run from the original request at each reached success
or late typed refusal. The refused branch advances only checked execution
and keeps the reached canonical body endpoint. -/
def LinkedMemoryWorkerBody (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (ComponentCall.Callee sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {pointer : FlatValue}
    (site : PayloadRoot.Site grow sig (.memory pointer)) (incoming : Config (core3 grow) (HostState sig))
    (actual : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  LinkedMemoryTransportBodyWith profile ready (ComponentCall.hostWithComponent bindings callees) bindings older site incoming
    (fun checkEntry canonEntry _ seen left right =>
      PublicTransportWorkerAlignment profile ready bindings callees older site incoming left right checkEntry canonEntry seen actual finish)
    (fun checkEntry canonEntry entered issue seen left right => PayloadPrefix.visible checkEntry = [] →
      PublicGiveWorkerAlignment profile ready bindings callees older site entered left right (.error issue)
        site.start incoming incoming checkEntry canonEntry [] seen actual finish)

/-- The real checked worker suffix at the flat public boundary. A late
refusal does not share its checked reply with the stopped canonical run. -/
def LinkedFlatWorkerBody (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (ComponentCall.Callee sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {type : Stored.TypeOf}
    (site : PayloadRoot.Site grow sig (.flat type)) (incoming : Config (core3 grow) (HostState sig))
    (actual : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  LinkedFlatTransportBodyWith profile ready (ComponentCall.hostWithComponent bindings callees) bindings older site incoming
    (fun checkEntry canonEntry entered words seen left right =>
      PublicSuccessTransport profile ready (ComponentCall.hostWithComponent bindings callees) bindings older
        site incoming entered checkEntry canonEntry words seen left right ∧
      PublicTransportWorkerAlignment profile ready bindings callees older site incoming left right checkEntry canonEntry seen actual finish)
    (fun checkEntry canonEntry entered issue seen left right => PayloadPrefix.visible checkEntry = [] →
      PublicGiveWorkerAlignment profile ready bindings callees older site entered left right (.error issue)
        site.start incoming incoming checkEntry canonEntry [] seen actual finish)

/-- The reached synchronous load stops at an actual short prefix or after
the exact store write, retaining both journals and the actual checked tail. -/
def CoreAcceptLoadCut (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (left right : Config (core3 grow) (HostState sig)) (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (leftTicket rightTicket : Nat) (loaded : CStore (core3 grow) × Except Core.Issue (Stored.OwnedMemory.Tree sig))
    (actual : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  let checked := { left with store := loaded.1, ctl := check.control (coreAcceptAfterLoad leftTicket loaded.2) }
  let raw := { right with store := loaded.1, ctl := canon.control (coreAcceptAfterLoad rightTicket loaded.2) }
  FramedComponentEarlyPrefix profile ready base bindings older check canon left right actual finish 3 ∨
    ∃ residual, actual = [.tau, .tau, .tau] ++ residual ∧
      (∀ place, ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready base)
        left place [.tau, .tau, .tau] checked place ∧
        ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base))
          right place [.tau, .tau, .tau] raw place) ∧
      VisitorWriterPath profile ready base bindings left right [.tau, .tau, .tau] [.tau, .tau, .tau] checked raw ∧
      PairedComponentSite older checked raw check canon ∧
      Steps profile ready (specDispatch ready base) checked residual finish

/-- The completed load's actual journal or registration segment. Agreement
on the reply words leaves both programs at their original caller frames.
A conflicting probe retains both branch programs and the checked suffix. -/
def CoreAcceptCompletionCut (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (start incoming : Config (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) (leftTicket rightTicket : Nat)
    (actual : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ leading trailing left right,
    actual = leading ++ trailing ∧
    PayloadPrefix.visible leading = [] ∧
    (∀ place, ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready base) start place leading left place ∧
      ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base))
        incoming place leading right place) ∧
    VisitorWriterPath profile ready base bindings start incoming leading leading left right ∧
    Steps profile ready (specDispatch ready base) left trailing finish ∧
    PairedComponentSite older left right check canon ∧
    (trailing = [] ∨ (∃ words, left.ctl = check.control (.pure (.flat words)) ∧ right.ctl = canon.control (.pure (.flat words))) ∨
      ∃ tree, RegistrationProbeMismatch start incoming left right check canon leftTicket rightTicket none tree)

/-- The compiler outcome of the selected request and its classification on
the actual finite checked run. The callback slice contains the visitor-derived
writer path, exact raw peer, occurrence transport, and checked residual. -/
structure ActualSelectedGive (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) {bindings : List (Binding sig)}
    {start : Config (core3 grow) (HostState sig)} {request : CoreGiveRequest bindings start}
    {route : GiveEffectRoute} (selection : request.Selected route)
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (incoming : Config (core3 grow) (HostState sig))
    (actual : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop where
  compiler :
    (∃ issue, selection.preflight = .error issue) ∨
      (∃ tag payload arity children field plan, selection.preflight = .ok (field, plan) ∧
        selection.tree = .tag ⟨tag, payload⟩ arity children ∧ (selection.site tag payload arity children field).Linked bindings)
  callback : CallbackSlice profile ready base bindings older start incoming actual finish

/-- After a common nested reply, follow the closed part of its actual
residual up to the next boundary. Only the original allocator occurrence
can authorize its pop, and only an executed pop exposes a new residual. -/
def RejoinedAllocatorResidual (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (ComponentCall.Callee sig))
    (retained : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (checkEntry canonEntry checked canonical : Config (core3 grow) (HostState sig))
    (checkTrace canonTrace actual : Trace grow sig) (finish : Config (core3 grow) (HostState sig))
    (first second : ReturnFrame.Continuation (core3 grow) (HostState sig)) : Prop :=
  open ReturnFrame.Occurrence in
  let base := ComponentCall.hostWithComponent bindings callees
  ∃ leading remaining lhs rhs mark,
    actual = leading ++ remaining ∧
    Steps profile ready (specDispatch ready base) checked leading lhs ∧
    Steps profile ready (specDispatch ready (host bindings base)) canonical leading rhs ∧
    Steps profile ready (specDispatch ready base) lhs remaining finish ∧
    AllocatorMark profile ready base bindings retained checkEntry canonEntry
      (checkTrace ++ leading) (canonTrace ++ leading) lhs rhs mark ∧
    ∀ value (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)),
      lhs.ctl = { cursor with frames := .prog first :: cursor.frames }.control (.pure value) →
      ActualMarkedPop profile ready base bindings retained checkEntry canonEntry lhs rhs
        (checkTrace ++ leading) (canonTrace ++ leading) mark cursor first second value remaining finish

/-- Compiled memory fragment consumed by the finite visitor. Compound nodes
carry layout evidence and the shapes of their active children. This is a
proof domain, not a runtime check for support. -/
inductive MemoryVisitShape : Stored.Endpoints.RecordLower.Field → Prop where
  | handle {item} : CanonicalHandle item → MemoryVisitShape item
  | scalar {type} {payload : Stored.Payload type} : PayloadPrefix.LocalDataType type → MemoryVisitShape (.data type payload)
  | string {item} : item.LayoutMatches (.prim .string) → item.Emitted → MemoryVisitShape item
  | aggregate {type items} : Stored.Endpoints.RecordLower.Field.LayoutMatches (.aggregate type items) type →
      (∀ item ∈ items, MemoryVisitShape item) → MemoryVisitShape (.aggregate type items)
  | fixed {element length entries} : entries.length = length →
      Stored.Endpoints.RecordLower.Field.EntriesMatch entries element →
      (∀ item ∈ entries, MemoryVisitShape item) → MemoryVisitShape (.fixed element length entries)
  | sum {type arms tag selected} :
      (∀ width, ABI.layout width type = ABI.variantLayout (arms.map (ABI.layoutOption width))) →
      (∀ item, selected = some item → some item.type ∈ arms) →
      (∀ item, selected = some item → MemoryVisitShape item) →
      MemoryVisitShape (.sum type arms tag selected)
  | list {element entries} : Stored.Endpoints.RecordLower.Field.EntriesMatch entries element →
      (∀ item ∈ entries, MemoryVisitShape item) → MemoryVisitShape (.dynamic (.list element) element entries)
  | map {key element entries} :
      Stored.Endpoints.RecordLower.Field.EntriesMatch entries (.record (ABI.mapEntryFields key element)) →
      Stored.Endpoints.RecordLower.Field.Emitted (.dynamic (.map key element) (.record (ABI.mapEntryFields key element)) entries) →
      (∀ keyField value, Stored.Endpoints.RecordLower.Field.aggregate (.record (ABI.mapEntryFields key element)) [keyField, value] ∈ entries →
        ∀ child ∈ [keyField, value], MemoryVisitShape child) →
      MemoryVisitShape (.dynamic (.map key element) (.record (ABI.mapEntryFields key element)) entries)

/-- Flat leaves, aggregates, fixed arrays, dynamic collections with placed entries and selected sums.
This is a proof domain, not a runtime check for support. -/
inductive FlatVisitShape : Stored.Endpoints.RecordLower.Field → Prop where
  | handle (item : Stored.Endpoints.RecordLower.Field) (nominal : CanonicalHandle item) : FlatVisitShape item
  | scalar (type : Stored.TypeOf) (data : PayloadPrefix.LocalDataType type) (payload : Stored.Payload type) :
      FlatVisitShape (.data type payload)
  | string (item : Stored.Endpoints.RecordLower.Field) (matched : item.LayoutMatches (.prim .string))
      (emitted : item.Emitted) : FlatVisitShape item
  | aggregate (type : Stored.TypeOf) (fields : List Stored.Endpoints.RecordLower.Field)
      (children : ∀ field ∈ fields, FlatVisitShape field) : FlatVisitShape (.aggregate type fields)
  | fixed (element : Stored.TypeOf) (length : Nat) (items : List Stored.Endpoints.RecordLower.Field)
      (children : ∀ field ∈ items, FlatVisitShape field) : FlatVisitShape (.fixed element length items)
  | collection (type element : Stored.TypeOf) (entries : List Stored.Endpoints.RecordLower.Field)
      (matching : Stored.Endpoints.RecordLower.Field.EntriesMatch entries element)
      (children : ∀ field ∈ entries, MemoryVisitShape field) : FlatVisitShape (.dynamic type element entries)
  | sum (type : Stored.TypeOf) (arms : List (Option Stored.TypeOf)) (tag : Nat)
      (selected : Option Stored.Endpoints.RecordLower.Field)
      (matched : Stored.Endpoints.RecordLower.Field.LayoutMatches (.sum type arms tag selected) type)
      (child : ∀ field, selected = some field → FlatVisitShape field) : FlatVisitShape (.sum type arms tag selected)

inductive FlatVisitFocus (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (origin : CStore (core3 grow))
    (checkNext : LinkedCallback.FlatSequenceCheckNext grow sig) (canonNext : LinkedCallback.FlatSequenceCanonNext grow sig)
    (left right : Config (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) : Prop where
  | returned (words : List FlatValue) (frame : LinkedCallback.ChildFrameOver older left right check canon)
      (growth : Core3.Grows origin.core left.store.core) (checked : left.ctl = check.control (checkNext (.ok words)))
      (canonical : right.ctl = canon.control (canonNext words)) : FlatVisitFocus older origin checkNext canonNext left right check canon
  | refused (issue : Stored.Endpoints.RecordLower.Issue) (checked : left.ctl = check.control (checkNext (.error issue))) :
      FlatVisitFocus older origin checkNext canonNext left right check canon

abbrev FlatVisitRun (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (origin : CStore (core3 grow))
    (checkNext : LinkedCallback.FlatSequenceCheckNext grow sig) (canonNext : LinkedCallback.FlatSequenceCanonNext grow sig) :=
  StringRunSliceWithWriters profile ready base bindings older (fun _ => FlatVisitFocus older origin checkNext canonNext)

def FlatVisitField (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (origin : CStore (core3 grow))
    (destination : RecordDestination) (inst : InstId) (budget : Nat) (item : Stored.Endpoints.RecordLower.Field) : Prop :=
  open PayloadPrefix Stored.Endpoints.RecordLower in
  ∀ index (checkNext : LinkedCallback.FlatSequenceCheckNext grow sig) (canonNext : LinkedCallback.FlatSequenceCanonNext grow sig)
      left right check canon,
    LinkedCallback.ChildFrameOver older left right check canon → Core3.Grows origin.core left.store.core →
    left.ctl = check.control (Stored.OwnedMemory.Claims.Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width item index .flat >>= checkNext) →
    right.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none (destination.context inst)
      destination.width item .flat >>= canonNext) →
    ∀ actual finish, Steps profile ready (specDispatch ready base) left actual finish → actual.length ≤ budget →
      FlatVisitRun profile ready base bindings older origin checkNext canonNext left right actual finish

/-- Keep the reached canonical program on a checked-only refusal, either
before the linked field or after the pop at an allocated collection tail. -/
inductive PendingMemoryField (destination : RecordDestination) (inst : InstId)
    (right : Config (core3 grow) (HostState sig)) : Prop where
  | field (peer : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) (item : Stored.Endpoints.RecordLower.Field)
      (address : Nat) (next : LinkedCallback.MemorySequence.CanonNext grow sig)
      (atField : right.ctl = peer.control (Stored.Endpoints.RecordLower.CanonicalTree.field Limits.spec Quirks.none
        (destination.context inst) destination.width item (.memory address) >>= next))
  | collection (peer : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) (entries : List Stored.Endpoints.RecordLower.Field)
      (area : ABI.Layout) (pointer address : Nat) (mode : Stored.Endpoints.RecordLower.CanonicalTree.EntryMode)
      (next : LinkedCallback.MemorySequence.CanonNext grow sig)
      (atTail : right.ctl = peer.control (PayloadPrefix.canonicalCollectionTail destination inst entries area (.memory address) pointer mode >>= next))

/-- A visitor can advance a sibling only after a common return. In a paused
allocator keep its current occurrence, even when that occurrence is lost. -/
inductive ValueVisitEnd (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (origin : CStore (core3 grow))
    (valueType : Type) (pending : Config (core3 grow) (HostState sig) → Prop)
    (checkNext : Except Stored.Endpoints.RecordLower.Issue valueType → Session grow sig (Ret (core3 grow)))
    (canonNext : valueType → Session grow sig (Ret (core3 grow)))
    (left right : Config (core3 grow) (HostState sig)) (trailing : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) :
    List (Option ReturnFrame.Occurrence.Location) → Prop where
  | returned (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) {value : valueType}
      (frame : LinkedCallback.ChildFrameOver older left right check canon) (growth : Core3.Grows origin.core left.store.core)
      (checked : left.ctl = check.control (checkNext (.ok value))) (canonical : right.ctl = canon.control (canonNext value)) :
      ValueVisitEnd profile ready base bindings older origin valueType pending checkNext canonNext left right trailing finish []
  | refused (issue : Stored.Endpoints.RecordLower.Issue) (check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
      (checked : left.ctl = check.control (checkNext (.error issue))) (atPending : pending right) :
      ValueVisitEnd profile ready base bindings older origin valueType pending checkNext canonNext left right trailing finish []
  | boundary {marks} (reached : StringSliceEnd profile ready base bindings older (fun _ _ _ _ _ => False)
      left right trailing finish marks) :
      ValueVisitEnd profile ready base bindings older origin valueType pending checkNext canonNext left right trailing finish marks
  | collectionInstall (exhausted : trailing = []) :
      ValueVisitEnd profile ready base bindings older origin valueType pending checkNext canonNext left right trailing finish []
  | collectionRange {target remaining marks} (nonempty : remaining ≠ [])
      (tail : Steps profile ready (specDispatch ready base) finish remaining target) :
      ValueVisitEnd profile ready base bindings older origin valueType pending checkNext canonNext left right trailing finish
        marks

/-- An actual checked derivation cut at a compiled visitor endpoint, with a
canonical path to its reached peer and all-location occurrence transport. -/
def ValueVisitRun (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (origin : CStore (core3 grow))
    (valueType : Type) (pending : Config (core3 grow) (HostState sig) → Prop)
    (checkNext : Except Stored.Endpoints.RecordLower.Issue valueType → Session grow sig (Ret (core3 grow)))
    (canonNext : valueType → Session grow sig (Ret (core3 grow)))
    (start incoming : Config (core3 grow) (HostState sig)) (actual : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ checked canonical trailing left right marks, actual = checked ++ trailing ∧
    PayloadPrefix.visible checked = PayloadPrefix.visible canonical ∧ left.store = right.store ∧
    OccurrenceTransport profile ready base bindings start incoming checked canonical left right marks ∧
    Steps profile ready (specDispatch ready base) left trailing finish ∧
    VisitorWriterPath profile ready base bindings start incoming checked canonical left right ∧
    ValueVisitEnd profile ready base bindings older origin valueType pending checkNext canonNext left right trailing finish marks

abbrev MemoryVisitEnd (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (origin : CStore (core3 grow))
    (destination : RecordDestination) (inst : InstId)
    (checkNext : LinkedCallback.MemorySequence.CheckNext grow sig) (canonNext : LinkedCallback.MemorySequence.CanonNext grow sig) :=
  ValueVisitEnd profile ready base bindings older origin Unit (PendingMemoryField destination inst) checkNext canonNext

abbrev MemoryVisitRun (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (origin : CStore (core3 grow))
    (destination : RecordDestination) (inst : InstId)
    (checkNext : LinkedCallback.MemorySequence.CheckNext grow sig) (canonNext : LinkedCallback.MemorySequence.CanonNext grow sig) :=
  ValueVisitRun profile ready base bindings older origin Unit (PendingMemoryField destination inst) checkNext canonNext

/-- A local comparison invoked on a real residual from a placed compiled
field. The budget refers to checked steps, not allocator or scheduler fuel. -/
def MemoryVisitField (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (origin : CStore (core3 grow))
    (destination : RecordDestination) (inst : InstId) (budget : Nat)
    (item : Stored.Endpoints.RecordLower.Field) (address : Nat) : Prop :=
  open PayloadPrefix Stored.Endpoints.RecordLower LinkedCallback.MemorySequence in
  ∀ index (checkNext : CheckNext grow sig) (canonNext : CanonNext grow sig) left right check canon,
    LinkedCallback.ChildFrameOver older left right check canon → Core3.Grows origin.core left.store.core →
    left.ctl = check.control (Stored.OwnedMemory.Claims.Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width item index (.memory address) >>= checkNext) →
    right.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width item (.memory address) >>= canonNext) →
    ∀ actual finish, Steps profile ready (specDispatch ready base) left actual finish → actual.length ≤ budget →
    MemoryVisitRun profile ready base bindings older origin destination inst checkNext canonNext left right actual finish

/-- Comparison of the actual remaining direct field program, including
its original completion continuation. This does not assert the program
pop or that a finite residual reaches the completion. -/
def DirectGiveVisitRun (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (request : GiveSelector bindings) (ticket : Nat)
    (left right : Config (core3 grow) (HostState sig)) (actual : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig)) : Prop :=
  match request.schema with
  | none => MemoryVisitRun profile ready base bindings older left.store request.destination request.inst
      (fun verdict => do return .flat (← writeCompletion (completion ticket (verdict.mapError Issue.lowerPayload |>.map (fun _ => 0)))))
      (fun _ => pure (.flat (completion 0 (.ok 0)).2)) left right actual finish
  | some schema => FlatVisitRun profile ready base bindings older left.store
      (fun verdict => do return .flat (← writeCompletion (flatCompletion ticket (ABI.flatten request.destination.width schema)
        (verdict.mapError Issue.lowerPayload))))
      (fun words => pure (.flat (flatCompletion 0 (ABI.flatten request.destination.width schema) (.ok words)).2))
      left right actual finish

/-- The executed checked-only reply leaves the exact canonical program
pending. Occurrences on the two sides now follow independent paths. -/
def MemoryVisitRefusedReply (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    {pointer : FlatValue} (site : PayloadRoot.Site grow sig (.memory pointer))
    (incoming left right : Config (core3 grow) (HostState sig)) (issue : Stored.Endpoints.RecordLower.Issue)
    (checkLeading canonLeading actual trailing : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  (trailing.length < 3 ∨
    CheckedOnlyGiveReply profile ready base bindings (.memory pointer) site.destination site.start.host.nextTicket issue
      site.start incoming left right checkLeading canonLeading trailing finish) ∧
    ∀ {label next}, GiveInstall bindings (specDispatch ready base) site.start label next →
      CallbackSlice profile ready base bindings older site.start incoming actual finish

/-- A common reply carries the complete request and its original occurrence
paths. A reached uncertified growth step is explicit, not silently replayed. -/
def GiveVisitCommonReply (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (value : route.output.Result) (incoming left right : Config (core3 grow) (HostState sig))
    (checkEntry checkBody canonLeading actual trailing : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  CheckedCoreReplyPrefix profile ready (specDispatch ready base) left trailing finish ∨ ∃ suffix checked canonical,
    trailing = [.tau, .tau, .tau] ++ suffix ∧ suffix.length < actual.length ∧
    Steps profile ready (specDispatch ready base) checked suffix finish ∧
    checked.host = left.host.record (route.reply site.destination site.start.host.nextTicket (.ok value)).1 ∧
    canonical.host = right.host ∧
    let checkFull := (checkEntry ++ checkBody) ++ [.tau, .tau, .tau]
    let canonFull := canonLeading ++ [.tau]
    (ExecutedCallbackSegment profile ready base bindings older site.start incoming checkFull canonFull checked canonical ∧
      CallbackSlice profile ready base bindings older site.start incoming (checkEntry ++ actual) finish) ∨
      (ReachedNonGrowingUpdate profile ready (specDispatch ready base) site.start checkFull checked ∧
        HostFrame.Related.Paired older checked canonical ∧
        OccurrenceTransport profile ready base bindings site.start incoming checkFull canonFull checked canonical ∧
        VisitorWriterPath profile ready base bindings site.start incoming checkFull canonFull checked canonical)

abbrev MemoryVisitCommonReply (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {pointer : FlatValue}
    (site : PayloadRoot.Site grow sig (.memory pointer)) :=
  GiveVisitCommonReply profile ready base bindings older site ()

/-- The reached visit retains both traces and the move used by all older
occurrences. A reply requires the original call occurrence at the top. -/
def MemoryVisitWithReply (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {pointer : FlatValue}
    (site : PayloadRoot.Site grow sig (.memory pointer)) (incoming entered : Config (core3 grow) (HostState sig))
    (checkEntry canonEntry actual : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  open ReturnFrame.Occurrence in
  ∃ checked canonical trailing left right marks, ∃ (move : Option Location → Option Location),
    actual = checked ++ trailing ∧ PayloadPrefix.visible checked = PayloadPrefix.visible canonical ∧ left.store = right.store ∧
    (∀ cursor, Trail profile ready (specDispatch ready base) site.checked cursor checked left (move cursor) ∧
      Trail profile ready (specDispatch ready (LiveDispatch.host bindings base)) entered cursor canonical right (move cursor)) ∧
    (∀ changes retained, OutsideMarks changes (segmentStorage site.checked) (segmentStorage entered) retained →
      OutsideMarks changes (segmentStorage left) (segmentStorage right) (marks ++ retained.map move)) ∧
    Steps profile ready (specDispatch ready base) left trailing finish ∧
    MemoryVisitEnd profile ready base bindings older site.checked.store site.destination site.inst
      site.reply site.referenceReply left right trailing finish marks ∧
    (move (some (.active 0 0)) = some (.active 0 0) →
      (marks = [] → (∃ (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)),
          LinkedCallback.ChildFrameOver older left right check canon ∧
          left.ctl = check.control (site.reply (.ok ())) ∧ right.ctl = canon.control (site.referenceReply ())) →
        MemoryVisitCommonReply profile ready base bindings older site incoming left right
          checkEntry checked (canonEntry ++ canonical) actual trailing finish) ∧
      ∀ issue (check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)), left.ctl = check.control (site.reply (.error issue)) →
        MemoryVisitRefusedReply profile ready base bindings older site incoming left right issue
          (checkEntry ++ checked) (canonEntry ++ canonical) (checkEntry ++ actual) trailing finish) ∧
    ∀ {label next}, GiveInstall bindings (specDispatch ready base) site.start label next →
      CallbackSlice profile ready base bindings older site.start incoming (checkEntry ++ actual) finish

/-- On the placed branch, distinguish a finite prefix inside entry from
an actually reached body. No canonical body path is used in the short case. -/
def ActualMemoryRequestRun (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {pointer : FlatValue}
    (site : PayloadRoot.Site grow sig (.memory pointer)) (incoming : Config (core3 grow) (HostState sig))
    (actual : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  open ReturnFrame.Occurrence in
  ∃ checkEntry, site.EntryPrefix profile ready base checkEntry site.checked ∧ PayloadPrefix.visible checkEntry = [] ∧
    ((∃ remaining, checkEntry = actual ++ remaining ∧ remaining ≠ [] ∧
      Steps profile ready (specDispatch ready base) finish remaining site.checked) ∨
    ∃ canonEntry entered body, actual = checkEntry ++ body ∧ PayloadPrefix.visible canonEntry = [] ∧
      (∀ place, Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base))
        incoming place canonEntry entered (site.entryPlace place)) ∧ entered.host = incoming.host ∧
      MemoryVisitWithReply profile ready base bindings older site incoming entered checkEntry canonEntry body finish) ∧
    ∀ {label next}, GiveInstall bindings (specDispatch ready base) site.start label next →
      CallbackSlice profile ready base bindings older site.start incoming actual finish

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LiveDispatch
