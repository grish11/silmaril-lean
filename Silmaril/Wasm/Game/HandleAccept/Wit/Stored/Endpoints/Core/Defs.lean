module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Session.Defs
public import Silmaril.Wasm.Component.Engine.Core3.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core

open Silmaril.Formats Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Game
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game.HandleAccept.Memory
open Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst
  (NodeIssue NodeMode NodeArgs checkNodeMode checkedCallout nodeOperands requireSome)
open Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Session (LinkIssue)
open Silmaril.Wasm.Game.Accept (Callout)

/-- Node loading does not invoke guest code or suspend the caller. Reject any operation
outside the supported call-local interpreter rather than dropping it from the trace. -/
inductive LocalIssue where
  | trapped (reason : TrapReason)
  | choice
  | coreCall
  | canonicalCall
  | scheduling
  | hostEffect
  deriving DecidableEq, Repr

/-- Run the reference load's read and update operations in order. The result retains
the store even when a later operation traps or needs an unsupported capability. -/
def runLocal {E : CoreEngine} {Value : Type} (program : P E Unit Value) (store : CStore E) :
    CStore E × Except LocalIssue Value :=
  match program with
  | .pure value => (store, .ok value)
  | .op op next =>
    match op with
    | .get => runLocal (next store) store
    | .modify update => runLocal (next ()) (update store)
    | .trap reason => (store, .error (.trapped reason))
    | .choose _ => (store, .error .choice)
    | .callCore _ _ => (store, .error .coreCall)
    | .call _ => (store, .error .canonicalCall)
    | .currentThread | .newThread _ | .block _ | .resumeThread _ => (store, .error .scheduling)
    | .hostGet | .hostSet _ | .emit _ => (store, .error .hostEffect)
termination_by structural program

inductive Issue where
  | unexpectedImport (target : Nat)
  | boundary (issue : NodeIssue)
  | stored (issue : Endpoints.Issue)
  | invalidChild (handle : BitVec 32)
  | exhaustedHandles
  | localEffect (issue : LocalIssue)
  deriving DecidableEq, Repr

/-- Component arena state persists across Core calls. The writer history observes
trees; only its separate held set authorizes endpoint transfer. -/
structure World (grow : SingleThreaded.GrowOracle) (sig : Signature) where
  reference : CStore (core3 grow)
  writer : Endpoints.State sig := {}

/-- The selected memory is linked by the Core instance, and the caller's component
instance supplies the canonical handle table. -/
structure Contract (sig : Signature) where
  code : Nat
  name : String × String
  tagOf : BitVec 32 → Option sig.Tag
  mode : NodeMode
  inst : InstId

variable {sig : Signature} {grow : SingleThreaded.GrowOracle}

def Contract.importType (contract : Contract sig) : FnType :=
  let tag : ScalarType := .num (.int .i32)
  let word : ScalarType := match contract.mode.address with
    | .i32 => tag
    | .i64 => .num (.int .i64)
  ⟨[tag, word, word, word], [tag]⟩

def Contract.link (contract : Contract sig) (module_ : Module) (instanceInfo : ScalarInstance)
    (initial : Config Nat) (memoryIndex : Nat) : Except LinkIssue (Option Nat) := do
  let actual := module_.imports[contract.code]?.map fun i => (i.moduleName, i.name)
  if actual ≠ some contract.name then throw (.wrongImport contract.code contract.name)
  if (module_.imports.filter fun i => (i.moduleName, i.name) == contract.name).length ≠ 1 then
    throw (.duplicateImport contract.name)
  if instanceInfo.imports[contract.code]? ≠ some contract.importType then
    throw (.wrongType contract.code contract.importType)
  return initial.frame.module.mems[memoryIndex]?

def childFromHistory {Value : Type} (history : List Value) (handle : BitVec 32) : Option Value := do
  let index := handle.toNat
  guard (0 < index && index ≤ history.length)
  history[history.length - index]?

def childAt (state : Endpoints.State sig) (handle : BitVec 32) : Option (Tree sig) :=
  childFromHistory state.accepted handle

def checkChildren (sig : Signature) (tag : sig.Tag) (historyLength childrenPtr count : Nat) : Except Issue Unit := do
  if !(sig.arity tag).Admits count then throw (.boundary .badArity)
  if childrenPtr % 4 ≠ 0 then throw (.boundary .unalignedChildren)
  if 4 * count > Component.Limits.spec.maxListBytes then throw (.boundary .childrenTooLong)
  if historyLength + 1 ≥ 2 ^ 32 then throw .exhaustedHandles

def decodeChildren {Value : Type} (observed : Callout) (history : List Value)
    (childrenPtr count : Nat) : Except Issue (List Value) := do
  let bytes ← requireSome (.boundary .childrenOutOfBounds) (observed.segment childrenPtr (4 * count))
  let handles ← requireSome (.boundary .badChildren) (le32s bytes)
  handles.mapM fun handle => requireSome (.invalidChild handle) (childFromHistory history handle)

/-- Shared argument checks after dispatch validates the target. The carrier supplies
its whole-schema check, not the guest. -/
def Contract.preflightOperands {Value : Type} (contract : Contract sig) (check : TypeOf → Except Stored.Issue Unit)
    (memory : Option Nat) (history : List Value) (call : UCall Nat) :
    Except Issue (NodeArgs sig.Tag × List Value) := do
  (checkNodeMode contract.mode).mapError .boundary
  let memory ← requireSome (.boundary .missingMemory) memory
  let observed ← (checkedCallout contract.name memory call contract.mode.address).mapError .boundary
  let (rawTag, payload, childrenPtr, count) ←
    requireSome (.boundary .badArguments) (nodeOperands contract.mode.address observed.args)
  let tag ← requireSome (.boundary (.unknownTag rawTag)) (contract.tagOf rawTag)
  (check (sig.payload tag)).mapError (Issue.stored ∘ Endpoints.Issue.lift)
  checkChildren sig tag history.length childrenPtr count
  let layout := ABI.layout contract.mode.address (sig.payload tag)
  if payload % layout.alignment.bytes ≠ 0 then throw (.boundary .unalignedPayload)
  let _ ← requireSome (.boundary .payloadOutOfBounds) (observed.segment payload layout.size)
  let children ← decodeChildren observed history childrenPtr count
  return (⟨tag, payload, childrenPtr, count⟩, children)

def Contract.preflight (contract : Contract sig) (memory : Option Nat) (writer : Endpoints.State sig)
    (call : UCall Nat) : Except Issue (NodeArgs sig.Tag × List (Tree sig)) := do
  if call.target != contract.code then throw (.unexpectedImport call.target)
  contract.preflightOperands checkSchema memory writer.accepted call

/-- Lift using the call's linear memory and persisted component arena. The temporary
Core projection supplies memory only: the reference node load cannot call into it. -/
def Contract.load (contract : Contract sig) (memory : Option Nat) (state : World grow sig)
    (call : UCall Nat) : CStore (core3 grow) × Except Issue (Tree sig) :=
  match contract.preflight memory state.writer call with
  | .error issue => (state.reference, .error issue)
  | .ok (args, children) =>
    let cx : LiftLowerContext (core3 grow) :=
      { opts := { memory, encoding := contract.mode.encoding }, inst := contract.inst }
    let live := { state.reference with core := { mems := call.store.mems } }
    let (after, result) := runLocal
      (buildNode sig Component.Limits.spec Quirks.none cx args.tag (.memory args.payload) children) live
    ({ after with core := state.reference.core },
      (result.mapError .localEffect).bind fun lifted => lifted.mapError (.stored ∘ .lift))

/-- Atomic accept-node: only after the complete canonical load and claim registration
can the writer publish a new tree and return its handle. -/
def Contract.attempt (contract : Contract sig) (memory : Option Nat) (state : World grow sig)
    (call : UCall Nat) : World grow sig × Except Issue (BitVec 32) :=
  let (reference, result) := contract.load memory state call
  match result.bind (fun tree => (state.writer.register tree).mapError .stored) with
  | .error issue => ({ state with reference }, .error issue)
  | .ok writer => (⟨reference, writer⟩, .ok (BitVec.ofNat 32 writer.accepted.length))

/-- Only the selected checked import is modeled. Errors retain their typed diagnostic
in `attempt` and reply with a call-local Core trap. -/
def Contract.answer (contract : Contract sig) (memory : Option Nat) (state : World grow sig)
    (call : UCall Nat) (reply : UReply) (updated : World grow sig) : Prop :=
  let (next, result) := contract.attempt memory state call
  updated = next ∧ reply = ⟨call.store, match result with
    | .ok handle => .values [.num ⟨.int .i32, handle⟩]
    | .error _ => .trap⟩

def Contract.env (contract : Contract sig) (grow : SingleThreaded.GrowOracle) (memory : Option Nat) :
    SEnv UImp :=
  ⟨World grow sig, contract.answer memory, fun _ _ => False⟩

/-- Linked sessions quantify all admitted export sequences, including ones following a
trapped call. Their component arena persists alongside the Core store. -/
def Contract.traces {Entry Input Output Exit : Type} (contract : Contract sig)
    (profile : Numerics.Profile) (module_ : Module) (memoryIndex : Nat) (state : World grow sig)
    (roles : IOAccept.Roles Entry Input Output Exit) :
    Set (List (Silmaril.Accept.IO.Tag Entry Input Output Exit)) :=
  { tags | ∃ moduleType instanceInfo initial,
    IsSpecInstance module_ moduleType instanceInfo initial ∧
    ∃ memory, contract.link module_ instanceInfo initial memoryIndex = .ok memory ∧
    ∃ phase pending current,
      IOAccept.TSession profile (contract.env grow memory) module_ memory roles initial state
        instanceInfo.addrs phase pending current tags }

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core
