module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Dispatch.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core.Scheduled

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Game
  Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Game.HandleAccept.Wit.Async (Channel Element Channel.endKind)

inductive Issue where
  | accept (reason : Core.Issue)
  | give (reason : Endpoints.Issue)
  | lower (reason : LocalIssue)
  | wrongContext
  | wrongType
  | ambiguousBinding
  | badSelection
  deriving DecidableEq, Repr

structure HostState (sig : Signature) where
  writer : Endpoints.State sig := {}
  refusals : List Issue := []

/-- A refusal is an explicit Core result, not a component-wide trap. The host retains
the typed reason. With two results, no valid handle or slot doubles as a sentinel. -/
def HostState.finish {sig : Signature} (state : HostState sig) : Except Issue Nat →
    HostState sig × List FlatValue
  | .ok value => (state, [i32Flat 0, i32Flat value])
  | .error issue => ({ state with refusals := issue :: state.refusals }, [i32Flat 1, i32Flat 0])

abbrev Session (grow : SingleThreaded.GrowOracle) (sig : Signature) (Value : Type) :=
  P (core3 grow) (HostState sig) Value

variable {sig : Signature} {grow : SingleThreaded.GrowOracle}

def acceptType (contract : Contract sig) : V1.FuncType :=
  let word := ABI.pointerType contract.mode.address
  ⟨[.int .i32, word, word, word], [.int .i32, .int .i32]⟩

def giveType : V1.FuncType := ⟨[.int .i32, .int .i32], [.int .i32, .int .i32]⟩

/-- The handoff import's authority is limited to one destination instance and an
endpoint kind and element schema chosen by the embedding at link time. -/
structure Handoff where
  name : String
  destination : InstId
  channel : Channel
  element : Element

def coreValue : FlatValue → Val
  | .int kind word => .num ⟨.int kind, word⟩
  | .float kind word => .num ⟨.float kind, word⟩

def allowed (inst : InstId) : Session grow sig Bool := do
  return (← currentInst?) == some inst && ((← getStore).inst? inst).any (·.mayLeave)

def finish (result : Except Issue Nat) : Session grow sig (List FlatValue) := do
  let (updated, reply) := (← hostGet).finish result
  hostSet updated
  return reply

def nodeCall (contract : Contract sig) (reference : CStore (core3 grow))
    (args : List FlatValue) : UCall Nat :=
  ⟨contract.code, { mems := reference.core.mems }, args.map coreValue⟩

def acceptAttempt (contract : Contract sig) (memory : Option Nat) (state : HostState sig)
    (reference : CStore (core3 grow)) (args : List FlatValue) :
    CStore (core3 grow) × HostState sig × List FlatValue :=
  let (updated, result) := contract.attempt memory (⟨reference, state.writer⟩ : World grow sig)
    (nodeCall contract reference args)
  let (after, reply) := ({ state with writer := updated.writer } : HostState sig).finish
    (result.mapError .accept |>.map BitVec.toNat)
  (updated.reference, after, reply)

/-- Run the same checked node load as the call-local Core host, against the live
memory of the scheduler. This synchronous import does not suspend the Core thread. -/
def accept (contract : Contract sig) (memory : Option Nat) (args : List FlatValue) :
    Session grow sig (List FlatValue) := do
  if !(← allowed contract.inst) then return ← finish (.error .wrongContext)
  let state ← hostGet
  let reference ← getStore
  let (updated, after, reply) := acceptAttempt contract memory state reference args
  modifyStore fun _ => updated
  hostSet after
  return reply

/-- A tree handle and root endpoint position select an observation only. A distinct
live claim, the arena kind/schema, and the caller's destination are all checked. -/
def give (contract : Handoff) (treeHandle position : BitVec 32) :
    Session grow sig (List FlatValue) := do
  if !(← allowed contract.destination) then return ← finish (.error .wrongContext)
  let state ← hostGet
  let some id := (childAt state.writer treeHandle).bind (fun tree => (rootIds tree)[position.toNat]?)
    | return ← finish (.error .badSelection)
  let .ok writer := state.writer.spend id | return ← finish (.error (.give .unclaimed))
  let reference ← getStore
  match Async.Transfer.readyToGive reference contract.channel contract.element ⟨id⟩ with
  | .error issue => finish (.error (.give (.give issue)))
  | .ok () =>
    hostSet { state with writer }
    let cx : LiftLowerContext (core3 grow) := { opts := {}, inst := contract.destination }
    let (updated, slot) := runLocal
      (lowerAsyncValue Limits.spec (contract.channel.endKind .read) cx id) reference
    modifyStore fun _ => updated
    finish (slot.mapError .lower)

def rejectBinding (issue : Issue) : Session grow sig (List FlatValue) := do
  let _ ← finish (.error issue)
  trap (.hostTrap "invalid acceptor import binding")

def dispatchImport (name : String) (contract : Contract sig) (memory : Option Nat) (handoff : Handoff)
    (called : String) (type : V1.FuncType) (args : List FlatValue) : Session grow sig (List FlatValue) := do
  if called == name then
    if name == handoff.name then return ← rejectBinding .ambiguousBinding
    if type != acceptType contract then return ← rejectBinding .wrongType
    return ← accept contract memory args
  if called != handoff.name then trap (.hostTrap "unlinked acceptor import")
  if type != giveType then return ← rejectBinding .wrongType
  match args with
  | [.int .i32 handle, .int .i32 position] => give handoff handle position
  | _ => finish (.error .wrongType)

/-- Resolve the selected memory in the linked writer instance; do not default to a
global address on a missing memory. Canonical async built-ins still use `specDispatch`. -/
def host (contract : Contract sig) (linked : ModuleInst) (memoryIndex : Nat) (handoff : Handoff) :
    HostImpl (core3 grow) (HostState sig) :=
  { HostImpl.none with
    embedder := dispatchImport contract.name.2 contract linked.mems[memoryIndex]? handoff }

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core.Scheduled
