module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core.Scheduled.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record.Defs
public import Silmaril.Wasm.Component.Reference.Validation.CanonOpts.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Component.ABI (StringEncoding)
open Silmaril.Wasm.Game.HandleAccept.Wit.Async (Channel Element Channel.endKind)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core (Contract)
open Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst (NodeMode)

inductive Issue where
  | accept (issue : Core.Issue)
  | claim (issue : Claims.Issue)
  | lowerRecord (issue : Endpoints.RecordLower.Issue)
  | lowerPayload (issue : Endpoints.RecordLower.Issue)
  | badLoweringMemory
  | badLoweringRealloc
  | wrongContext
  | wrongType
  | wrongPassingMode
  | wrongPayloadType
  | wrongResultType
  | unlinkedImport
  | ambiguousBinding
  | badSelection
  | stalePendingAccept
  | subtaskTableFull
  deriving DecidableEq, Repr

/-- Import tickets distinguish reentrant calls to the same binding. A canonical trap is
observed in the machine's labels; the started call has no status return in this journal. -/
inductive Event where
  | entered (ticket : Nat) (name : String) (type : V1.FuncType) (args : List FlatValue)
  | published (ticket : Nat) (handle : Nat)
  | returned (ticket : Nat) (value : Nat)
  | returnedFlat (ticket : Nat) (values : List FlatValue)
  | refused (ticket : Nat) (issue : Issue)
  | bindingTrap (ticket : Nat) (issue : Issue)
  | queued (ticket : Nat)
  | cancelled (ticket : Nat)
  deriving BEq

structure PendingAccept where
  caller : CallerId
  subtask : SubtaskId
  callee : HostFuncId
  inst : InstId
  ticket : Nat

structure HostState (sig : Signature) where
  writer : State sig := {}
  nextTicket : Nat := 0
  newestFirst : List Event := []
  pendingAccepts : List PendingAccept := []

variable {sig : Signature}

def HostState.transcript (state : HostState sig) : List Event := state.newestFirst.reverse

def Event.publication : Event → Option (Nat × Nat)
  | .published ticket handle => some (ticket, handle)
  | _ => none

def HostState.publications (state : HostState sig) : List (Nat × Nat) :=
  state.transcript.filterMap Event.publication

def HostState.refusals (state : HostState sig) : List Issue :=
  state.newestFirst.filterMap fun
    | .refused _ issue | .bindingTrap _ issue => some issue
    | _ => none

def HostState.enter (state : HostState sig) (name : String) (type : V1.FuncType)
    (args : List FlatValue) : HostState sig :=
  { state with
    nextTicket := state.nextTicket + 1
    newestFirst := .entered state.nextTicket name type args :: state.newestFirst }

def HostState.record (state : HostState sig) (event : Event) : HostState sig :=
  { state with newestFirst := event :: state.newestFirst }

def completion (ticket : Nat) : Except Issue Nat → Event × List FlatValue
  | .ok value => (.returned ticket value, [i32Flat 0, i32Flat value])
  | .error issue => (.refused ticket issue, [i32Flat 1, i32Flat 0])

def zeroWord : NumType → FlatValue
  | .int kind => .int kind 0
  | .float kind => .float kind 0

/-- A Core-only multivalue import convention: status, then the linked payload vector.
Refusals carry typed zero padding. The defensive shape check is after lowering:
a `wrongResultType` refusal does not undo completed canonical effects. -/
def flatCompletion (ticket : Nat) (shape : List NumType) (result : Except Issue (List FlatValue)) :
    Event × List FlatValue :=
  let refuse := fun issue => (Event.refused ticket issue, i32Flat 1 :: shape.map zeroWord)
  match result with
  | .error issue => refuse issue
  | .ok values =>
    if values.map Stored.flatType = shape then (.returnedFlat ticket values, i32Flat 0 :: values)
    else refuse .wrongResultType

/-- The journal is append-only; neither a callback nor a trap can roll back its entries. -/
def Extends (before after : HostState sig) : Prop :=
  before.transcript <+: after.transcript ∧ before.nextTicket ≤ after.nextTicket

/-- The only changes to authority are publication of a newly lifted root and spending a
specific identity. A new successful lift may reacquire an endpoint, but a resource arena
identity already observed in an accepted root cannot be registered again. -/
inductive WriterStep : State sig → State sig → Prop where
  | same (state : State sig) : WriterStep state state
  | publish {before after : State sig} (tree : Tree sig)
      (registered : before.register tree = .ok after) : WriterStep before after
  | spend (state : State sig) (update : Spend) : WriterStep state (update.apply state)

inductive WriterRun : State sig → State sig → Prop where
  | refl (state : State sig) : WriterRun state state
  | cons {before next after : State sig} (step : WriterStep before next)
      (rest : WriterRun next after) : WriterRun before after

/-- Every publication has a journal entry, including in runs ending before the Core reply. -/
def PublicationDelta (before after : HostState sig) : Prop :=
  ∃ entries, after.publications = before.publications ++ entries ∧
    after.writer.accepted.length = before.writer.accepted.length + entries.length ∧
    ∀ index ticket handle, entries[index]? = some (ticket, handle) →
      handle = before.writer.accepted.length + index + 1 ∧ handle < 2 ^ 32

def CheckedWrite (before after : HostState sig) : Prop :=
  Extends before after ∧ WriterStep before.writer after.writer ∧ PublicationDelta before after

abbrev Session (grow : SingleThreaded.GrowOracle) (sig : Signature) (Result : Type) :=
  P (core3 grow) (HostState sig) Result

structure RecordDestination where
  memory : Nat
  width : AddrType
  realloc : Option Nat := none
  encoding : StringEncoding := .utf8

def RecordDestination.link (linked : ModuleInst) (memoryIndex : Nat) (width : AddrType)
    (encoding : StringEncoding) (reallocIndex : Option Nat) : Except Issue RecordDestination := do
  let some memory := linked.mems[memoryIndex]? | throw .badLoweringMemory
  let some realloc := reallocIndex.mapM (fun index => linked.funcs[index]?) | throw .badLoweringRealloc
  return ⟨memory, width, realloc, encoding⟩

def RecordDestination.check {grow : SingleThreaded.GrowOracle} (destination : RecordDestination)
    (reference : CStore (core3 grow)) :
    Except Issue Unit := do
  if (core3 grow).memAddrType? reference.core destination.memory != some destination.width then
    throw .badLoweringMemory
  if let some realloc := destination.realloc then
    let type := ((core3 grow).funcType? reference.core realloc).bind (core3 grow).flatType?
    if type != some (Silmaril.Wasm.Component.Validation.reallocType destination.width) then
      throw .badLoweringRealloc

def RecordDestination.context {grow : SingleThreaded.GrowOracle} (destination : RecordDestination)
    (inst : InstId) : LiftLowerContext (core3 grow) :=
  { inst
    opts := { memory := some destination.memory, realloc := destination.realloc, encoding := destination.encoding } }

/-- Import capabilities fix the destination and nominal type at link time. Core passes
an accepted tree index and a position within that root's observations, never an arena ID. -/
inductive Action (sig : Signature) where
  | accept (contract : Contract sig) (memory : Option Nat)
  | acceptFlat (source : FlatSource sig)
  | giveOwner (resource : RtId)
  | dropOwner (resource : RtId)
  | giveEndpoint (channel : Channel) (element : Element)
  | giveRecord (destination : RecordDestination)
  | givePayload (destination : RecordDestination)
  | giveFlat (destination : RecordDestination) (payload : Stored.TypeOf)

structure Binding (sig : Signature) where
  name : String
  inst : InstId
  action : Action sig

variable {grow : SingleThreaded.GrowOracle}

def Binding.accept (contract : Contract sig) (linked : ModuleInst) (memoryIndex : Nat) : Binding sig :=
  ⟨contract.name.2, contract.inst, .accept contract linked.mems[memoryIndex]?⟩

def Binding.acceptFlat (name : String × String) (inst : InstId) (linked : ModuleInst) (memoryIndex : Nat)
    (mode : NodeMode) (tag : sig.Tag) : Except Issue (Binding sig) := do
  if mode.asynchronous then throw (.accept (.boundary (.boundary .asyncCall)))
  if mode.passing != .flat then throw .wrongPassingMode
  (checkFlatSchema (sig.payload tag)).mapError .accept
  let some memory := linked.mems[memoryIndex]? | throw (.accept (.boundary (.boundary .missingMemory)))
  return ⟨name.2, inst, .acceptFlat ⟨name, inst, memory, mode.address, mode.encoding, tag⟩⟩

def Binding.giveRecord (name : String) (inst : InstId) (linked : ModuleInst) (memoryIndex : Nat)
    (width : AddrType) (encoding : StringEncoding) (reallocIndex : Option Nat := none) :
    Except Issue (Binding sig) :=
  (RecordDestination.link linked memoryIndex width encoding reallocIndex).map fun dest =>
    ⟨name, inst, .giveRecord dest⟩

/-- Use the same linked memory ABI for any supported WIT payload root. -/
def Binding.givePayload (name : String) (inst : InstId) (linked : ModuleInst) (memoryIndex : Nat)
    (width : AddrType) (encoding : StringEncoding) (reallocIndex : Option Nat := none) :
    Except Issue (Binding sig) :=
  (RecordDestination.link linked memoryIndex width encoding reallocIndex).map fun dest =>
    ⟨name, inst, .givePayload dest⟩

def Binding.giveFlat (name : String) (inst : InstId) (linked : ModuleInst) (memoryIndex : Nat)
    (width : AddrType) (encoding : StringEncoding) (payload : Stored.TypeOf) (reallocIndex : Option Nat := none) :
    Except Issue (Binding sig) := do
  (OwnedMemory.checkSchema payload).mapError (.lowerPayload ∘ .preflight ∘ .schema)
  let dest ← RecordDestination.link linked memoryIndex width encoding reallocIndex
  return ⟨name, inst, .giveFlat dest payload⟩

def Binding.type (binding : Binding sig) : V1.FuncType :=
  match binding.action with
  | .accept contract _ => Endpoints.Core.Scheduled.acceptType contract
  | .acceptFlat source =>
    let word := ABI.pointerType source.width
    ⟨word :: word :: ABI.flatten source.width (sig.payload source.tag), [.int .i32, .int .i32]⟩
  | .giveRecord destination | .givePayload destination =>
    ⟨[.int .i32, ABI.pointerType destination.width], [.int .i32, .int .i32]⟩
  | .giveFlat destination payload => ⟨[.int .i32], .int .i32 :: ABI.flatten destination.width payload⟩
  | _ => Endpoints.Core.Scheduled.giveType

def writeCompletion (reply : Event × List FlatValue) : Session grow sig (List FlatValue) := do
  hostSet ((← hostGet).record reply.1)
  return reply.2

def finish (ticket : Nat) (result : Except Issue Nat) : Session grow sig (List FlatValue) :=
  writeCompletion (completion ticket result)

def publishRootAt (ticket : Nat) (tree : Tree sig) (expected : Option Nat) :
    Session grow sig (Except Issue Nat) := do
  let current ← hostGet
  match current.writer.register tree with
  | .error issue => return .error (.accept (.claims issue))
  | .ok writer =>
    let handle := writer.accepted.length
    if expected.any (· != handle) then return .error .wrongResultType
    if handle ≥ 2 ^ 32 then return .error (.accept (.boundary .exhaustedHandles))
    hostSet (({ current with writer } : HostState sig).record (.published ticket handle))
    return .ok handle

def publishRoot (ticket : Nat) (tree : Tree sig) : Session grow sig (Except Issue Nat) :=
  publishRootAt ticket tree none

def acceptWith (ticket : Nat) (loadNode : World grow sig → CStore (core3 grow) × Except Core.Issue (Tree sig)) :
    Session grow sig (Except Issue Nat) := do
  let state ← hostGet
  let reference ← getStore
  let (updated, result) := loadNode ⟨reference, state.writer⟩
  modifyStore fun _ => updated
  match result with
  | .error issue => return .error (.accept issue)
  | .ok tree => publishRoot ticket tree

def accept (ticket : Nat) (contract : Contract sig) (memory : Option Nat) (args : List FlatValue) :
    Session grow sig (Except Issue Nat) :=
  acceptWith ticket fun state => load contract memory state (Endpoints.Core.Scheduled.nodeCall contract state.reference args)

def select (handle : BitVec 32) : Session grow sig (Option (Tree sig)) := do
  return Endpoints.Core.childFromHistory (← hostGet).writer.accepted handle

/-- Embed the claims program without snapshotting diagnostics. In particular the update
that spends an owner precedes a possibly reentrant canonical destructor call. -/
def claims : Access (core3 grow) (HostState sig) sig where
  read := return (← hostGet).writer
  spend update := do
    let current ← hostGet
    hostSet { current with writer := update.apply current.writer }

def recordClaims : Record.Access (core3 grow) (HostState sig) sig where
  read := claims.read
  spendOwner id := claims.spend (.owner id)
  spendEndpoint id := claims.spend (.endpoint id)

def selectMemoryDestination (destination : RecordDestination) (args : List FlatValue) :
    Session grow sig (Except Issue (Tree sig × Nat)) := do
  let [.int .i32 handle, pointer] := args | return .error .wrongType
  if Stored.flatType pointer != ABI.pointerType destination.width then return .error .wrongType
  if let .error issue := destination.check (← getStore) then return .error issue
  let some tree ← select handle | return .error .badSelection
  return .ok (tree, flatNat pointer)

def giveToMemory (inst : InstId) (destination : RecordDestination) (args : List FlatValue)
    (lower : LiftLowerContext (core3 grow) → Tree sig → Nat →
      Session grow sig (Except Endpoints.RecordLower.Issue Unit))
    (diagnose : Endpoints.RecordLower.Issue → Issue) :
    Session grow sig (Except Issue Nat) := do
  match ← selectMemoryDestination destination args with
  | .error issue => return .error issue
  | .ok (tree, ptr) =>
    return (← lower (destination.context inst) tree ptr) |>.mapError diagnose |>.map (fun _ => 0)

def giveRecord (inst : InstId) (destination : RecordDestination) (args : List FlatValue) :
    Session grow sig (Except Issue Nat) :=
  giveToMemory inst destination args (fun cx tree ptr =>
    Record.lowerRoot recordClaims Limits.spec Quirks.none cx tree (.memory ptr)) .lowerRecord

def givePayload (inst : InstId) (destination : RecordDestination) (args : List FlatValue) :
    Session grow sig (Except Issue Nat) :=
  giveToMemory inst destination args (fun cx tree ptr =>
    Record.lowerPayloadRoot recordClaims Limits.spec Quirks.none cx tree (.memory ptr)) .lowerPayload

def rootHasSchema (tree : Tree sig) (type : Stored.TypeOf) : Bool :=
  match tree with
  | .atom impossible => impossible.elim
  | .tag payload _ _ => decide (sig.payload payload.1 = type)

def selectFlatDestination (destination : RecordDestination) (payload : Stored.TypeOf)
    (args : List FlatValue) : Session grow sig (Except Issue (Tree sig)) := do
  let [.int .i32 handle] := args | return .error .wrongType
  if let .error issue := destination.check (← getStore) then return .error issue
  let some tree ← select handle | return .error .badSelection
  if !rootHasSchema tree payload then return .error .wrongPayloadType
  return .ok tree

/-- Type selection is a preflight check on the accepted tree. It cannot spend a claim
or enter realloc; the emitter handles effects only after it succeeds. -/
def giveFlat (inst : InstId) (destination : RecordDestination) (payload : Stored.TypeOf)
    (args : List FlatValue) : Session grow sig (Except Issue (List FlatValue)) := do
  if (← currentInst?) != some inst || !((← getStore).inst? inst).any (·.mayLeave) then
    return .error .wrongContext
  match ← selectFlatDestination destination payload args with
  | .error issue => return .error issue
  | .ok tree =>
    return (← Record.lowerPayloadRoot recordClaims Limits.spec Quirks.none
      (destination.context inst) tree .flat).mapError .lowerPayload

def withTree (args : List FlatValue) (use : Tree sig → Nat → Session grow sig (Except Issue Nat)) :
    Session grow sig (Except Issue Nat) := do
  match args with
  | [.int .i32 handle, .int .i32 position] =>
    let some tree ← select handle | return .error .badSelection
    use tree position.toNat
  | _ => return .error .wrongType

/-- Canonical give and drop run in the live scheduler. Typed refusals are status pairs;
an actual destructor or canonical lower trap is not converted into an ordinary refusal. -/
def invoke (ticket : Nat) (binding : Binding sig) (args : List FlatValue) : Session grow sig (Except Issue Nat) := do
  if (← currentInst?) != some binding.inst || !((← getStore).inst? binding.inst).any (·.mayLeave) then
    return .error .wrongContext
  let cx : LiftLowerContext (core3 grow) := { opts := {}, inst := binding.inst }
  match binding.action with
  | .accept contract memory =>
    if contract.inst != binding.inst then return .error .wrongContext
    accept ticket contract memory args
  | .acceptFlat source =>
    if source.inst != binding.inst then return .error .wrongContext
    acceptWith ticket fun state => source.load state args
  | .giveOwner resource => withTree args fun tree position => do
    let some receipt := (rootReceipts tree)[position]? | return .error .badSelection
    return (← claims.give Limits.spec cx resource (receiptId receipt)).mapError .claim
  | .dropOwner resource => withTree args fun tree position => do
    let some receipt := (rootReceipts tree)[position]? | return .error .badSelection
    let result ← claims.drop (destructorCall Limits.spec Quirks.none) resource (receiptId receipt)
    return result.mapError .claim |>.map (fun _ => 0)
  | .giveEndpoint channel element => withTree args fun tree position => do
    let some id := (rootEndpoints tree)[position]? | return .error .badSelection
    return (← claims.giveEndpoint Limits.spec cx channel element ⟨id⟩).mapError .claim
  | .giveRecord destination => giveRecord binding.inst destination args
  | .givePayload destination => givePayload binding.inst destination args
  | .giveFlat _ _ => return .error .wrongType

def rejectBinding (ticket : Nat) (issue : Issue) : Session grow sig (List FlatValue) := do
  hostSet ((← hostGet).record (.bindingTrap ticket issue))
  trap (.hostTrap "invalid mixed acceptor import binding")

def resolveBinding (bindings : List (Binding sig)) (name : String) (type : V1.FuncType) :
    Except Issue (Binding sig) :=
  match bindings.filter (·.name == name) with
  | [] => .error .unlinkedImport
  | [binding] =>
    if type != binding.type then .error .wrongType else .ok binding
  | _ => .error .ambiguousBinding

def route (ticket : Nat) (bindings : List (Binding sig)) (name : String) (type : V1.FuncType)
    (args : List FlatValue) : Session grow sig (List FlatValue) := do
  match resolveBinding bindings name type with
  | .error issue => rejectBinding ticket issue
  | .ok binding =>
    match binding.action with
    | .giveFlat destination payload =>
      let result ← giveFlat binding.inst destination payload args
      writeCompletion (flatCompletion ticket (ABI.flatten destination.width payload) result)
    | _ => finish ticket (← invoke ticket binding args)

def dispatchImport (bindings : List (Binding sig)) (name : String) (type : V1.FuncType)
    (args : List FlatValue) : Session grow sig (List FlatValue) := do
  let state ← hostGet
  hostSet (state.enter name type args)
  route state.nextTicket bindings name type args

def host (bindings : List (Binding sig)) : HostImpl (core3 grow) (HostState sig) :=
  { HostImpl.none with embedder := dispatchImport bindings }

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
