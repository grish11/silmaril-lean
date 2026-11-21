module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadRoot.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.PublicCollection

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Execution.Core
open Stored.Endpoints Stored.Endpoints.RecordLower
open PayloadPrefix

/-- The selected dynamic root and the actual parked public call. The checked
and reference paths use the same starting store and parked Core activation. -/
structure Site (grow : SingleThreaded.GrowOracle) (sig : Signature) where
  start : State grow sig
  route : GiveEffectRoute
  destination : RecordDestination
  inst : InstId
  name : String
  functionType : V1.FuncType
  handle : BitVec IntType.i32.width
  tag : sig.Tag
  payload : OwnedMemory.Payload (sig.payload tag)
  arity : Nat
  children : Fin arity → OwnedMemory.Tree sig
  type : TypeOf
  element : TypeOf
  entries : List Field
  thread : Option ThreadId
  core : (core3 grow).Thread (CanonHost (core3 grow))
  resume : List FlatValue → Session grow sig (Ret (core3 grow))
  frames : List (Seg (core3 grow) (HostState sig))
  rest : List (Activation (core3 grow) (HostState sig))

variable {grow : SingleThreaded.GrowOracle} {sig : Signature}

def Site.tree (site : Site grow sig) : OwnedMemory.Tree sig := .tag ⟨site.tag, site.payload⟩ site.arity site.children

def Site.field (site : Site grow sig) : Field := .dynamic site.type site.element site.entries

def Site.toRoot (site : Site grow sig) : PayloadRoot.Site grow sig site.route :=
  ⟨site.start, site.destination, site.inst, site.name, site.functionType, site.handle, site.tag, site.payload, site.arity,
    site.children, site.field, site.thread, site.core, site.resume, site.frames, site.rest⟩

def Site.cursor (site : Site grow sig) : Cursor (E := core3 grow) (HostState sig) :=
  ⟨site.thread, .core site.core site.resume :: site.frames, site.rest⟩

def Site.reply (site : Site grow sig) (verdict : Except RecordLower.Issue site.route.output.Result) :
    Session grow sig (Ret (core3 grow)) := do
  return .flat (← writeCompletion (site.route.reply site.destination site.start.host.nextTicket verdict))

def Site.withBody (site : Site grow sig) (program : Session grow sig (Ret (core3 grow))) : State grow sig :=
  { site.start with host := site.start.host.enter site.name site.functionType (site.route.args site.handle)
                    ctl := site.cursor.control program }

def Site.checkedBody (site : Site grow sig) : Session grow sig (Ret (core3 grow)) :=
  Record.Effects.field recordClaims Limits.spec Quirks.none (site.destination.context site.inst)
    site.destination.width site.field 0 site.route.output >>= site.reply

abbrev Site.ReferenceNext (site : Site grow sig) := site.route.output.Result → Session grow sig (Ret (core3 grow))

noncomputable def Site.reference (site : Site grow sig) (next : site.ReferenceNext) : State grow sig :=
  let cx := site.destination.context site.inst
  let schema := sig.payload site.tag
  let value := site.payload.val.value
  let program := Lower.Output.rec (motive := fun out => Session grow sig out.Result)
    (fun ptr => store Limits.spec Quirks.none cx value schema ptr)
    (lowerFlatAt Limits.spec Quirks.none cx site.destination.width value schema) site.route.output
  { site.start with ctl := site.cursor.control (program >>= next) }

def Site.area (site : Site grow sig) : Layout := layout site.destination.width site.element

def Site.checkResume (site : Site grow sig) : ReturnFrame.Continuation (core3 grow) (HostState sig) :=
  checkedCollectionResume site.destination site.inst site.entries site.area 0 site.route.output site.reply

def Site.referenceResume (site : Site grow sig) (next : site.ReferenceNext) :
    ReturnFrame.Continuation (core3 grow) (HostState sig) :=
  canonicalCollectionResume site.destination site.inst site.entries site.area site.route.output next

def Site.checkEntry (site : Site grow sig) (ready : HostReady (HostState sig)) (bindings : List (Binding sig)) :
    State grow sig :=
  collectionEntry site.destination site.inst site.area site.entries.length
    (specDispatch ready (host bindings)) (site.withBody site.checkedBody) site.cursor site.checkResume

noncomputable def Site.referenceEntry (site : Site grow sig) (ready : HostReady (HostState sig)) (bindings : List (Binding sig))
    (next : site.ReferenceNext) : State grow sig :=
  collectionEntry site.destination site.inst site.area site.entries.length
    (specDispatch ready (host bindings)) (site.reference next) site.cursor (site.referenceResume next)

/-- Admission evidence for the actual linked call and selected compiled root.
Live claim checks, ABI fit, and memory placement are not assumed here. -/
structure Site.Linked (site : Site grow sig) (bindings : List (Binding sig)) : Prop where
  parked : site.start.ctl = ⟨site.thread, .core site.core site.resume, site.frames⟩ :: site.rest
  calling : (core3 grow).status site.start.store.core site.core = .callout (.embedder site.name site.functionType)
    (site.route.args site.handle)
  linked : resolveBinding bindings site.name site.functionType = .ok ⟨site.name, site.inst, site.route.action site.destination⟩
  caller : Plain.callerInstance site.start.store site.thread = .ok (some site.inst)
  mayLeave : (site.start.store.inst? site.inst).any (·.mayLeave) = true
  destination : site.destination.check site.start.store = .ok ()
  selected : Endpoints.Core.childFromHistory site.start.host.writer.accepted site.handle = some site.tree
  admitted : site.route.admits site.destination site.tree
  compiled : ∃ plan, Record.preflightValue (site.destination.context (grow := grow) site.inst) (sig.payload site.tag)
    site.payload site.route.output = .ok (site.field, plan)
  mode : CanonicalTree.EntryMode.forOutput site.destination.width site.type site.route.output = .value

def Site.TailRule (site : Site grow sig) (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (reached : State grow sig) (pointer : Nat) : Prop :=
  ReachedCollectionTail profile ready bindings site.destination site.inst site.entries site.area site.route.output 0 pointer reached

/-- A public call either stops before allocation, or actually installs both
allocator frames. Any supplied classified finite prefix is replayed from that
installation; if it reaches a natural return, the child rules can continue it. -/
inductive Outcome (site : Site grow sig) (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (next : site.ReferenceNext) (children : State grow sig → Nat → Prop) : Prop where
  | refused (issue : RecordLower.Issue) {labels} (silent : visible labels = []) :
      Steps profile ready (specDispatch ready (host bindings)) site.start labels (site.withBody (site.reply (.error issue))) →
      Outcome site profile ready bindings next children
  | placementTrap (reason : TrapReason) (count : Nat)
      (verdict : rootPlacement site.destination site.start.store (sig.payload site.tag) site.route.output = .error reason) :
      Steps profile ready (specDispatch ready (host bindings)) site.start (List.replicate count .tau ++ [.trap reason])
        (StepDefs.trapCfg (site.withBody site.checkedBody)) → Outcome site profile ready bindings next children
  | installed {leftLabels rightLabels} (leftSilent : visible leftLabels = []) (rightSilent : visible rightLabels = [])
      (lhs : Steps profile ready (specDispatch ready (host bindings)) site.start leftLabels (site.checkEntry ready bindings))
      (rhs : Steps profile ready (specDispatch ready (host bindings)) (site.reference next) rightLabels
        (site.referenceEntry ready bindings next))
      (paired : HostFrame.Paired site.checkResume (site.referenceResume next) (site.checkEntry ready bindings)
        (site.referenceEntry ready bindings next))
      (returns : ∀ {last seen} (_path : Prefix profile ready bindings site.checkResume (site.checkEntry ready bindings) seen last)
        (reached : Cursor (E := core3 grow) (HostState sig)) (pointer : Nat),
        last.ctl = { reached with frames := .prog site.checkResume :: reached.frames }.control (pure (.nat pointer)) →
        children last pointer →
        CollectionCut profile ready bindings site.checkResume (site.referenceResume next) site.start (site.reference next)
          { last with ctl := reached.control (site.checkResume (.nat pointer)) } reached site.reply next seen) :
      Outcome site profile ready bindings next children

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.PublicCollection
