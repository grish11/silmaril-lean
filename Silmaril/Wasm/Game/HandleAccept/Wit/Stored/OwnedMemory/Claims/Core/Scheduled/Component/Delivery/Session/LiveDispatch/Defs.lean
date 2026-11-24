module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.CanonicalEntry.Defs
public import Silmaril.Wasm.Component.Reference.Machine.HostFrame.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LiveDispatch

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Stored.Endpoints

variable {grow : SingleThreaded.GrowOracle} {sig : Signature}

def admit {Result : Type} (inst : InstId) (selection : Session grow sig (Except Issue Result)) :
    Session grow sig (Except Issue Result) := do
  if (← currentInst?) != some inst || !((← getStore).inst? inst).any (·.mayLeave) then
    return .error .wrongContext
  selection

noncomputable def memoryBody (inst : InstId) (destination : RecordDestination) (tree : Tree sig) (ptr : Nat) :
    Session grow sig (List FlatValue) :=
  match tree with
  | .atom impossible => impossible.elim
  | .tag payload _ _ =>
    store Limits.spec Quirks.none (destination.context inst) payload.2.val.value (sig.payload payload.1) ptr >>=
      fun _ => pure (completion 0 (.ok 0)).2

noncomputable def flatBody (inst : InstId) (destination : RecordDestination) (schema : Stored.TypeOf) (tree : Tree sig) :
    Session grow sig (List FlatValue) :=
  match tree with
  | .atom impossible => impossible.elim
  | .tag payload _ _ =>
    lowerFlatAt Limits.spec Quirks.none (destination.context inst) destination.width payload.2.val.value
        (sig.payload payload.1) >>= fun words => pure (flatCompletion 0 (ABI.flatten destination.width schema) (.ok words)).2

/-- Caller, ABI and root-selection failures return the existing boundary status words.
Recursive checked guards are compared as stopped prefixes, not simulated by a canonical error. -/
noncomputable def memoryWords (inst : InstId) (destination : RecordDestination) (args : List FlatValue) :
    Session grow sig (List FlatValue) :=
  admit inst (selectMemoryDestination destination args) >>= fun
    | .error issue => pure (completion 0 (.error issue)).2
    | .ok (tree, ptr) => memoryBody inst destination tree ptr

noncomputable def flatWords (inst : InstId) (destination : RecordDestination) (schema : Stored.TypeOf)
    (args : List FlatValue) : Session grow sig (List FlatValue) :=
  admit inst (selectFlatDestination destination schema args) >>= fun
    | .error issue => pure (flatCompletion 0 (ABI.flatten destination.width schema) (.error issue)).2
    | .ok tree => flatBody inst destination schema tree

def selectBinding (bindings : List (Binding sig)) (name : String) (kind : V1.FuncType) :
    Option (InstId × RecordDestination × Option Stored.TypeOf) :=
  match resolveBinding bindings name kind with
  | .ok ⟨_, inst, .givePayload destination⟩ => some (inst, destination, none)
  | .ok ⟨_, inst, .giveFlat destination schema⟩ => some (inst, destination, some schema)
  | _ => none

/-- Each occurrence resolves the link and reads the live caller, memory and accepted roots.
Non-give handlers retain the underlying dispatcher, including its open hooks. Reference
gives do not append checked entry/completion events. Reply words do not encode the ticket. -/
noncomputable def host (bindings : List (Binding sig)) (base : HostImpl (core3 grow) (HostState sig)) :
    HostImpl (core3 grow) (HostState sig) :=
  { base with embedder := fun name kind args =>
      match selectBinding bindings name kind with
      | none => base.embedder name kind args
      | some (inst, destination, none) => memoryWords inst destination args
      | some (inst, destination, some schema) => flatWords inst destination schema args }

def Unchanged (bindings : List (Binding sig)) : Call (core3 grow) → Prop
  | .hostCallout (.embedder name kind) _ => selectBinding bindings name kind = none
  | _ => True

/-- Only a give request about to be dispatched is excluded. A suspended give,
allocator frame, or a future give in ordinary guest code is not excluded. -/
structure UnchangedAt (bindings : List (Binding sig)) (state : Config (core3 grow) (HostState sig)) : Prop where
  direct : ∀ {thread call next frames rest}, state.ctl = ⟨thread, .prog (.op (.call call) next), frames⟩ :: rest →
    Unchanged bindings call
  core : ∀ {thread core next frames rest callee args}, state.ctl = ⟨thread, .core core next, frames⟩ :: rest →
    (core3 grow).status state.store.core core = .callout callee args → Unchanged bindings (.hostCallout callee args)

def UnchangedThrough (bindings : List (Binding sig)) (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig))
    (start : Config (core3 grow) (HostState sig)) (labels : List (Label (core3 grow) (HostState sig)))
    (finish : Config (core3 grow) (HostState sig)) : Prop :=
  ∀ {leading cut label trailing}, labels = leading ++ label :: trailing →
    Steps profile ready (specDispatch ready base) start leading cut →
    Steps profile ready (specDispatch ready base) cut (label :: trailing) finish → UnchangedAt bindings cut

/-- The actual step about to install an overlaid give. Suspended calls and
unexecuted requests in a continuation do not count as installations. -/
inductive GiveInstall (bindings : List (Binding sig))
    (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))) :
    Config (core3 grow) (HostState sig) → Label (core3 grow) (HostState sig) →
      Config (core3 grow) (HostState sig) → Prop where
  | direct {state thread call next frames rest}
      (focused : state.ctl = ⟨thread, .prog (.op (.call call) next), frames⟩ :: rest)
      (give : ¬ Unchanged bindings call) :
      GiveInstall bindings dispatch state .tau
        { state with ctl := ⟨thread, .prog (dispatch call), .prog next :: frames⟩ :: rest }
  | core {state thread core next frames rest callee args}
      (focused : state.ctl = ⟨thread, .core core next, frames⟩ :: rest)
      (calling : (core3 grow).status state.store.core core = .callout callee args)
      (give : ¬ Unchanged bindings (.hostCallout callee args)) :
      GiveInstall bindings dispatch state .tau
        { state with ctl := ⟨thread, .prog (dispatch (.hostCallout callee args)), .core core next :: frames⟩ :: rest }

/-- The exact Core request at a pending public give. No caller, selection,
preflight, or return verdict is inferred from resolving the binding. -/
structure CoreGiveRequest (bindings : List (Binding sig)) (state : Config (core3 grow) (HostState sig)) where
  name : String
  kind : V1.FuncType
  args : List FlatValue
  inst : InstId
  destination : RecordDestination
  schema : Option Stored.TypeOf
  thread : Option ThreadId
  core : (core3 grow).Thread (CanonHost (core3 grow))
  next : List FlatValue → Session grow sig (Ret (core3 grow))
  frames : List (Seg (core3 grow) (HostState sig))
  rest : List (Activation (core3 grow) (HostState sig))
  focused : state.ctl = ⟨thread, .core core next, frames⟩ :: rest
  calling : (core3 grow).status state.store.core core = .callout (.embedder name kind) args
  linked : resolveBinding bindings name kind = .ok ⟨name, inst,
    schema.elim (.givePayload destination) (.giveFlat destination)⟩

/-- The public selector's result before entering the recursive emitter. -/
abbrev SelectionValue (sig : Signature) : Option Stored.TypeOf → Type
  | none => Tree sig × Nat
  | some _ => Tree sig

def SelectionValue.tree : (schema : Option Stored.TypeOf) → SelectionValue sig schema → Tree sig
  | none, selected => selected.1
  | some _, selected => selected

def SelectionValue.output : (schema : Option Stored.TypeOf) → SelectionValue sig schema → Lower.Output
  | none, selected => .memory selected.2
  | some _, _ => .flat

/-- The reached link supplies the selector for either kind of caller. The
selector itself does not carry a program or Core return frame. -/
structure GiveSelector (bindings : List (Binding sig)) where
  name : String
  kind : V1.FuncType
  args : List FlatValue
  inst : InstId
  destination : RecordDestination
  schema : Option Stored.TypeOf
  linked : resolveBinding bindings name kind = .ok ⟨name, inst,
    schema.elim (.givePayload destination) (.giveFlat destination)⟩

def CoreGiveRequest.selector {bindings : List (Binding sig)} {state : Config (core3 grow) (HostState sig)}
    (request : CoreGiveRequest bindings state) : GiveSelector bindings :=
  ⟨request.name, request.kind, request.args, request.inst, request.destination, request.schema, request.linked⟩

def GiveSelector.program {bindings : List (Binding sig)} (request : GiveSelector bindings) :
    Session grow sig (Except Issue (SelectionValue sig request.schema)) :=
  match request.schema with
  | none => admit request.inst (selectMemoryDestination request.destination request.args)
  | some schema => admit request.inst (selectFlatDestination request.destination schema request.args)

/-- Evidence from the live selector, before any preparation or lowering. -/
structure GiveSelector.Admitted {bindings : List (Binding sig)} (request : GiveSelector bindings)
    (start : Config (core3 grow) (HostState sig)) (thread : Option ThreadId)
    (selected : SelectionValue sig request.schema) : Prop where
  caller : Plain.callerInstance start.store thread = .ok (some request.inst)
  mayLeave : (start.store.inst? request.inst).any (·.mayLeave) = true
  unconfined : threadMayLeave start.store thread = true
  destination : request.destination.check start.store = .ok ()
  selectedRoute : ∃ (route : GiveEffectRoute) (handle : BitVec IntType.i32.width),
    request.args = route.args handle ∧ route.output = SelectionValue.output request.schema selected ∧
    route.admits request.destination (SelectionValue.tree request.schema selected) ∧
    resolveBinding bindings request.name request.kind = .ok ⟨request.name, request.inst, route.action request.destination⟩ ∧
    Stored.Endpoints.Core.childFromHistory start.host.writer.accepted handle = some (SelectionValue.tree request.schema selected)

open PayloadRoot in
def checkedTail (inst : InstId) (destination : RecordDestination) (ticket : Nat) :
    (schema : Option Stored.TypeOf) → Except Issue (SelectionValue sig schema) → Session grow sig (List FlatValue)
  | none, result =>
    (match result with
     | .error issue => pure (.error issue)
     | .ok (tree, ptr) => do
       let lowered ← Stored.OwnedMemory.Claims.Record.lowerPayloadRoot recordClaims Limits.spec Quirks.none
         (destination.context inst) tree (.memory ptr)
       return lowered.mapError Issue.lowerPayload |>.map (fun _ => 0)) >>= Stored.OwnedMemory.Claims.Core.Scheduled.finish ticket
  | some schema, result =>
    (match result with
     | .error issue => pure (.error issue)
     | .ok tree => do
       let lowered ← Stored.OwnedMemory.Claims.Record.lowerPayloadRoot recordClaims Limits.spec Quirks.none
         (destination.context inst) tree .flat
       return lowered.mapError Issue.lowerPayload) >>= fun lowered =>
      writeCompletion (flatCompletion ticket (ABI.flatten destination.width schema) lowered)

noncomputable def referenceTail (inst : InstId) (destination : RecordDestination) :
    (schema : Option Stored.TypeOf) → Except Issue (SelectionValue sig schema) → Session grow sig (List FlatValue)
  | none, .error issue => pure (completion 0 (.error issue)).2
  | none, .ok (tree, ptr) => memoryBody inst destination tree ptr
  | some schema, .error issue => pure (flatCompletion 0 (ABI.flatten destination.width schema) (.error issue)).2
  | some schema, .ok tree => flatBody inst destination schema tree

def GiveSelector.checkedEntry {bindings : List (Binding sig)} (request : GiveSelector bindings) :
    Session grow sig (Nat × Except Issue (SelectionValue sig request.schema)) := do
  let state ← hostGet
  hostSet (state.enter request.name request.kind request.args)
  let verdict ← request.program
  return (state.nextTicket, verdict)

def GiveSelector.checkedContinuation {bindings : List (Binding sig)} (request : GiveSelector bindings)
    (store : CStore (core3 grow)) (thread : Option ThreadId)
    (selected : Nat × Except Issue (SelectionValue sig request.schema)) : Session grow sig (Ret (core3 grow)) :=
  let words := checkedTail request.inst request.destination selected.1 request.schema selected.2
  (if threadMayLeave store thread then words else confine words) >>= fun reply => pure (.flat reply)

noncomputable def GiveSelector.canonicalContinuation {bindings : List (Binding sig)} (request : GiveSelector bindings)
    (store : CStore (core3 grow)) (thread : Option ThreadId)
    (selected : Except Issue (SelectionValue sig request.schema)) : Session grow sig (Ret (core3 grow)) :=
  let words := referenceTail request.inst request.destination request.schema selected
  (if threadMayLeave store thread then words else confine words) >>= fun reply => pure (.flat reply)

/-- Compile the root selected by the live callout, before any authority
preparation, placement check, or payload effect. -/
def GiveSelector.preflight {bindings : List (Binding sig)} (request : GiveSelector bindings)
    (selected : SelectionValue sig request.schema) : Except RecordLower.Issue (RecordLower.Field × List RecordLower.Object) :=
  match SelectionValue.tree request.schema selected with
  | .atom impossible => impossible.elim
  | .tag payload _ _ => Record.preflightValue (request.destination.context (grow := grow) request.inst)
      (sig.payload payload.1) payload.2 (SelectionValue.output request.schema selected)

/-- The checked program for a successfully compiled root. Preparation, width,
fit and placement are still effects of the program, not admission facts. -/
def compiledRoot (inst : InstId) (destination : RecordDestination) {type : Stored.TypeOf}
    (payload : Stored.OwnedMemory.Payload type) (field : RecordLower.Field) (plan : List RecordLower.Object)
    (output : Lower.Output) : Session grow sig (Except RecordLower.Issue output.Result) :=
  let context := destination.context (grow := grow) inst
  RecordLower.Internal.lowerWithPlan Quirks.none context (Record.authority recordClaims Limits.spec context)
    type payload.val.value (.ok (field, plan)) RecordLower.Field.objects
    (fun width item => Record.Effects.root recordClaims Limits.spec Quirks.none context width type item output)

def compiledTail (destination : RecordDestination) (ticket : Nat)
    (lower : {type : Stored.TypeOf} → Stored.OwnedMemory.Payload type →
      (output : Lower.Output) → Session grow sig (Except RecordLower.Issue output.Result)) :
    (schema : Option Stored.TypeOf) → SelectionValue sig schema → Session grow sig (Ret (core3 grow))
  | none, (tree, ptr) => match tree with
    | .atom impossible => impossible.elim
    | .tag root _ _ => do
      let verdict ← lower root.2 (.memory ptr)
      return .flat (← writeCompletion (completion ticket (verdict.mapError Issue.lowerPayload |>.map (fun _ => 0))))
  | some schema, tree => match tree with
    | .atom impossible => impossible.elim
    | .tag root _ _ => do
      let verdict ← lower root.2 .flat
      return .flat (← writeCompletion (flatCompletion ticket (ABI.flatten destination.width schema)
        (verdict.mapError Issue.lowerPayload)))

def GiveSelector.compiledContinuation {bindings : List (Binding sig)} (request : GiveSelector bindings)
    (ticket : Nat) (selected : SelectionValue sig request.schema)
    (field : RecordLower.Field) (plan : List RecordLower.Object) : Session grow sig (Ret (core3 grow)) :=
  compiledTail request.destination ticket (fun payload output => compiledRoot request.inst request.destination payload field plan output)
    request.schema selected

/-- The fit check at the pointer width read by the checked program. -/
def GiveSelector.selectedFits {bindings : List (Binding sig)} (request : GiveSelector bindings)
    (selected : SelectionValue sig request.schema) (width : AddrType) : Bool :=
  match SelectionValue.tree request.schema selected with
  | .atom impossible => impossible.elim
  | .tag payload _ _ => Lower.fits Quirks.none request.destination.encoding width (sig.payload payload.1) payload.2.val.value

/-- The checked program at the reached width, before placement. -/
def GiveSelector.measuredContinuation {bindings : List (Binding sig)} (request : GiveSelector bindings)
    (ticket : Nat) (selected : SelectionValue sig request.schema) (field : RecordLower.Field)
    (width : AddrType) : Session grow sig (Ret (core3 grow)) :=
  let context := request.destination.context (grow := grow) request.inst
  compiledTail request.destination ticket
    (fun {type} payload output =>
      if !Lower.fits Quirks.none context.opts.encoding width type payload.val.value then
        pure (.error (.preflight (.abi .allocationPrecondition)))
      else Record.Effects.root recordClaims Limits.spec Quirks.none context width type field output)
    request.schema selected

/-- The fit-success branch starts the actual route-specific placement program. -/
def GiveSelector.placementContinuation {bindings : List (Binding sig)} (request : GiveSelector bindings)
    (ticket : Nat) (selected : SelectionValue sig request.schema) (field : RecordLower.Field)
    (width : AddrType) : Session grow sig (Ret (core3 grow)) :=
  let context := request.destination.context (grow := grow) request.inst
  compiledTail request.destination ticket
    (fun {type} _ output => Record.Effects.root recordClaims Limits.spec Quirks.none context width type field output)
    request.schema selected

/-- The placement check for the selected route and nominal root. -/
def GiveSelector.selectedPlacement {bindings : List (Binding sig)} (request : GiveSelector bindings)
    (selected : SelectionValue sig request.schema) (store : CStore (core3 grow)) : Except TrapReason Unit :=
  match SelectionValue.tree request.schema selected with
  | .atom impossible => impossible.elim
  | .tag payload _ _ => PayloadPrefix.rootPlacement request.destination store (sig.payload payload.1)
      (SelectionValue.output request.schema selected)

/-- The compiled field visitor, with the original public completion still
attached, after the route's placement check has succeeded. -/
def GiveSelector.fieldContinuation {bindings : List (Binding sig)} (request : GiveSelector bindings)
    (ticket : Nat) (selected : SelectionValue sig request.schema) (field : RecordLower.Field) :
    Session grow sig (Ret (core3 grow)) :=
  compiledTail request.destination ticket
    (fun _ output => Record.Effects.field recordClaims Limits.spec Quirks.none (request.destination.context request.inst)
      request.destination.width field 0 output) request.schema selected

/-- Continuation after the checked preparation reads. A refused preparation
returns through the checked completion only; success still reads the width. -/
def GiveSelector.preparedContinuation {bindings : List (Binding sig)} (request : GiveSelector bindings)
    (ticket : Nat) (selected : SelectionValue sig request.schema) (field : RecordLower.Field)
    (prepared : Except RecordLower.Issue Unit) : Session grow sig (Ret (core3 grow)) :=
  let context := request.destination.context (grow := grow) request.inst
  compiledTail request.destination ticket
    (fun {type} payload output => match prepared with
      | .error issue => pure (.error issue)
      | .ok () => do
        let width ← ptrType context
        if !Lower.fits Quirks.none context.opts.encoding width type payload.val.value then
          return .error (.preflight (.abi .allocationPrecondition))
        Record.Effects.root recordClaims Limits.spec Quirks.none context width type field output)
    request.schema selected

def CoreGiveRequest.selectionProgram {bindings : List (Binding sig)} {state : Config (core3 grow) (HostState sig)}
    (request : CoreGiveRequest bindings state) : Session grow sig (Except Issue (SelectionValue sig request.schema)) :=
  request.selector.program

/-- The checked journal records the ticket; either caller sees only status
and ABI-typed padding. -/
def giveAdmissionReply (ticket : Nat) (destination : RecordDestination) (schema : Option Stored.TypeOf)
    (issue : Issue) : Event × List FlatValue :=
  schema.elim (completion ticket (.error issue))
    (fun schema => flatCompletion ticket (ABI.flatten destination.width schema) (.error issue))

def CoreGiveRequest.admissionReply {bindings : List (Binding sig)} {state : Config (core3 grow) (HostState sig)}
    (request : CoreGiveRequest bindings state) (issue : Issue) : Event × List FlatValue :=
  giveAdmissionReply state.host.nextTicket request.destination request.schema issue

/-- The one journal read actually demanded by the guarded selector. Wrong
callers, invalid argument words and invalid destinations do not consult it.
The flat schema check itself comes after this read. -/
def giveLookupDemand (store : CStore (core3 grow)) (thread : Option ThreadId) (inst : InstId)
    (destination : RecordDestination) (schema : Option Stored.TypeOf) (args : List FlatValue) : Option (BitVec IntType.i32.width) :=
  match Plain.callerInstance store thread with
  | .error _ => none
  | .ok caller =>
    if caller != some inst || !(store.inst? inst).any (·.mayLeave) then none
    else match schema, args with
    | none, [.int .i32 handle, pointer] =>
      if Stored.flatType pointer != ABI.pointerType destination.width then none
      else if let .error _ := destination.check store then none else some handle
    | some _, [.int .i32 handle] =>
      if let .error _ := destination.check store then none else some handle
    | _, _ => none

def GiveSelector.lookupDemand {bindings : List (Binding sig)} (request : GiveSelector bindings)
    (store : CStore (core3 grow)) (thread : Option ThreadId) : Option (BitVec IntType.i32.width) :=
  giveLookupDemand store thread request.inst request.destination request.schema request.args

def CoreGiveRequest.lookupDemand {bindings : List (Binding sig)} {state : Config (core3 grow) (HostState sig)}
    (request : CoreGiveRequest bindings state) : Option (BitVec IntType.i32.width) :=
  giveLookupDemand state.store request.thread request.inst request.destination request.schema request.args

/-- A direct program call has a program return frame, not the parked Core
caller of the two public give routes. Its actual focus is kept separate. -/
def DirectGiveAt (bindings : List (Binding sig)) (state : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ name kind args thread next frames rest inst destination schema,
    state.ctl = ⟨thread, .prog (.op (.call (.hostCallout (.embedder name kind) args)) next), frames⟩ :: rest ∧
    resolveBinding bindings name kind = .ok ⟨name, inst, Option.elim schema (.givePayload destination) (.giveFlat destination)⟩

/-- The result of the read-only admission and selection prefix. The tree is
an observation from the live journal, not evidence of a live transfer claim. -/
structure CoreGiveRequest.Selected {bindings : List (Binding sig)} {state : Config (core3 grow) (HostState sig)}
    (request : CoreGiveRequest bindings state) (route : GiveEffectRoute) where
  handle : BitVec IntType.i32.width
  tree : Tree sig
  args : request.args = route.args handle
  linked : resolveBinding bindings request.name request.kind =
    .ok ⟨request.name, request.inst, route.action request.destination⟩
  caller : Plain.callerInstance state.store request.thread = .ok (some request.inst)
  mayLeave : (state.store.inst? request.inst).any (·.mayLeave) = true
  destination : request.destination.check state.store = .ok ()
  selected : Stored.Endpoints.Core.childFromHistory state.host.writer.accepted handle = some tree
  admitted : route.admits request.destination tree

/-- The live canonical cursor immediately after successful selection. Its
emitter has not started, even if the checked compiler refuses the payload. -/
noncomputable def CoreGiveRequest.Selected.canonicalPending {bindings : List (Binding sig)}
    {state : Config (core3 grow) (HostState sig)} {request : CoreGiveRequest bindings state}
    {route : GiveEffectRoute} (selection : request.Selected route) : Config (core3 grow) (HostState sig) :=
  let body := match route with
    | .memory pointer => memoryBody request.inst request.destination selection.tree (flatNat pointer)
    | .flat schema => flatBody request.inst request.destination schema selection.tree
  { state with ctl := ⟨request.thread, .prog (body >>= fun words => pure (.flat words)),
      .core request.core request.next :: request.frames⟩ :: request.rest }

def CoreGiveRequest.Selected.site {bindings : List (Binding sig)} {state : Config (core3 grow) (HostState sig)}
    {request : CoreGiveRequest bindings state} {route : GiveEffectRoute} (selection : request.Selected route)
    (tag : sig.Tag) (payload : OwnedMemory.Payload (sig.payload tag))
    (arity : Nat) (children : Fin arity → Tree sig) (field : RecordLower.Field) : PayloadRoot.Site grow sig route :=
  ⟨state, request.destination, request.inst, request.name, request.kind, selection.handle, tag, payload, arity,
    children, field, request.thread, request.core, request.next, request.frames, request.rest⟩

/-- The actual selected payload's pure compiler check, before any memory
placement, claim preparation, or realloc action. -/
def CoreGiveRequest.Selected.preflight {bindings : List (Binding sig)} {state : Config (core3 grow) (HostState sig)}
    {request : CoreGiveRequest bindings state} {route : GiveEffectRoute} (selection : request.Selected route) :
    Except RecordLower.Issue (RecordLower.Field × List RecordLower.Object) :=
  match selection.tree with
  | .atom impossible => impossible.elim
  | .tag payload _ _ => Record.preflightValue (request.destination.context (grow := grow) request.inst)
    (sig.payload payload.1) payload.2 route.output

/-- A compiler rejection writes the checked ticketed error and rejoins the
parked Core caller without starting the recursive body. -/
def CoreGiveRequest.Selected.compilerRefused {bindings : List (Binding sig)} {state : Config (core3 grow) (HostState sig)}
    {request : CoreGiveRequest bindings state} {route : GiveEffectRoute} (selection : request.Selected route)
    (issue : RecordLower.Issue) : Config (core3 grow) (HostState sig) :=
  let reply := route.reply request.destination state.host.nextTicket (.error issue)
  { state with host := (state.host.enter request.name request.kind (route.args selection.handle)).record reply.1
               ctl := ⟨request.thread, .core ((core3 grow).resume state.store.core request.core (.values reply.2))
                 request.next, request.frames⟩ :: request.rest }

/-- Replay up to the first reached give installation, divergent host read, or
substituted return. At an installation the live run stops before installing any
body. At a read or return both actual steps execute. The rest is evidence about
the baseline only and is not claimed for the live run. -/
inductive PairedReplay (bindings : List (Binding sig)) (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (start incoming : Config (core3 grow) (HostState sig)) (labels : List (Label (core3 grow) (HostState sig)))
    (finish : Config (core3 grow) (HostState sig)) : Prop where
  | complete {other}
      (replay : Steps profile ready (specDispatch ready (host bindings base)) incoming labels other)
      (paired : HostFrame.Related.Paired older finish other)
  | request {leading label trailing beforeLeft beforeRight afterLeft}
      (split : labels = leading ++ label :: trailing)
      (baseline : Steps profile ready (specDispatch ready base) start leading beforeLeft)
      (replay : Steps profile ready (specDispatch ready (host bindings base)) incoming leading beforeRight)
      (paired : HostFrame.Related.Paired older beforeLeft beforeRight)
      (install : GiveInstall bindings (specDispatch ready base) beforeLeft label afterLeft)
      (tail : Steps profile ready (specDispatch ready base) afterLeft trailing finish)
  | boundary {leading label trailing beforeLeft beforeRight afterLeft afterRight}
      (split : labels = leading ++ label :: trailing)
      (baseline : Steps profile ready (specDispatch ready base) start leading beforeLeft)
      (replay : Steps profile ready (specDispatch ready (host bindings base)) incoming leading beforeRight)
      (paired : HostFrame.Related.Paired older beforeLeft beforeRight)
      (boundary : HostFrame.Related.Boundary older beforeLeft beforeRight label afterLeft afterRight)
      (baselineStep : Step profile ready (specDispatch ready base) beforeLeft label afterLeft)
      (replayedStep : Step profile ready (specDispatch ready (host bindings base)) beforeRight label afterRight)
      (tail : Steps profile ready (specDispatch ready base) afterLeft trailing finish)

/-- A compared nested give either rejoins its local caller with the older
frames still paired, or reaches an actual read or older-frame pop. In the
second case only the executed prefix (including the boundary) has replayed. -/
inductive NestedReplay (profile : ProfileKind) (ready : HostReady (HostState sig))
    (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (body incoming : Config (core3 grow) (HostState sig))
    (labels : List (Label (core3 grow) (HostState sig))) (checked : Config (core3 grow) (HostState sig)) : Prop where
  | rejoined {reached}
      (run : Steps profile ready dispatch incoming labels reached)
      (paired : HostFrame.Related.Paired older checked reached)
  | boundary {leading label trailing beforeLeft beforeRight afterLeft afterRight}
      (split : labels = leading ++ label :: trailing)
      (baseline : Steps profile ready dispatch body leading beforeLeft)
      (replay : Steps profile ready dispatch incoming leading beforeRight)
      (paired : HostFrame.Related.Paired older beforeLeft beforeRight)
      (boundary : HostFrame.Related.Boundary older beforeLeft beforeRight label afterLeft afterRight)
      (baselineStep : Step profile ready dispatch beforeLeft label afterLeft)
      (replayedStep : Step profile ready dispatch beforeRight label afterRight)

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LiveDispatch
