module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core (Contract runLocal)
open Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst (NodeArgs checkedCallout)

inductive Issue where
  | boundary (issue : Endpoints.Core.Issue)
  | localEffect (issue : Endpoints.Core.LocalIssue)
  | claims (issue : Claims.Issue)
  deriving DecidableEq, Repr

structure World (grow : SingleThreaded.GrowOracle) (sig : Signature) where
  reference : CStore (core3 grow)
  writer : State sig := {}

variable {sig : Signature} {grow : SingleThreaded.GrowOracle}

def preflight (contract : Contract sig) (memory : Option Nat) (state : World grow sig)
    (call : UCall Nat) : Except Issue (NodeArgs sig.Tag × List (Tree sig)) := do
  if call.target != contract.code then throw (.boundary (.unexpectedImport call.target))
  (contract.preflightOperands OwnedMemory.checkSchema memory state.writer.accepted call).mapError .boundary

def load (contract : Contract sig) (memory : Option Nat) (state : World grow sig)
    (call : UCall Nat) : CStore (core3 grow) × Except Issue (Tree sig) :=
  match preflight contract memory state call with
  | .error issue => (state.reference, .error issue)
  | .ok (args, children) =>
    let cx : LiftLowerContext (core3 grow) :=
      { opts := { memory, encoding := contract.mode.encoding }, inst := contract.inst }
    let live := { state.reference with core := { mems := call.store.mems } }
    let (after, result) := runLocal
      (OwnedMemory.buildNode sig Component.Limits.spec Quirks.none cx args.tag (.memory args.payload) children) live
    ({ after with core := state.reference.core },
      (result.mapError .localEffect).bind fun lifted => lifted.mapError (Issue.claims ∘ Claims.Issue.lift))

/-- A fixed tag selects the flat WIT schema. Child handles and indirect list/string
contents are still read from the linked memory. This import does not suspend the caller. -/
structure FlatSource (sig : Signature) where
  name : String × String
  inst : InstId
  memory : Nat
  width : AddrType
  encoding : ABI.StringEncoding
  tag : sig.Tag

def checkFlatSchema (payload : Stored.TypeOf) : Except Issue Unit :=
  (OwnedMemory.checkSchema payload).mapError (.claims ∘ .lift ∘ .schema)

def FlatSource.preflight (source : FlatSource sig) (state : World grow sig) (args : List FlatValue) :
    Except Issue (List FlatValue × List (Tree sig)) := do
  checkFlatSchema (sig.payload source.tag)
  let call : UCall Nat := ⟨0, { mems := state.reference.core.mems }, []⟩
  let observed ← (checkedCallout source.name source.memory call source.width).mapError (.boundary ∘ .boundary)
  let pointer :: count :: payload := args | throw (.boundary (.boundary .badArguments))
  let word := ABI.pointerType source.width
  if Stored.flatType pointer != word || Stored.flatType count != word then
    throw (.boundary (.boundary .badArguments))
  if payload.map Stored.flatType != ABI.flatten source.width (sig.payload source.tag) then
    throw (.claims (.lift (.schema .flatTypes)))
  (Endpoints.Core.checkChildren sig source.tag state.writer.accepted.length (flatNat pointer)
    (flatNat count)).mapError .boundary
  let children ← (Endpoints.Core.decodeChildren observed state.writer.accepted (flatNat pointer)
    (flatNat count)).mapError .boundary
  return (payload, children)

def FlatSource.load (source : FlatSource sig) (state : World grow sig) (args : List FlatValue) :
    CStore (core3 grow) × Except Issue (Tree sig) :=
  match source.preflight state args with
  | .error issue => (state.reference, .error issue)
  | .ok (payload, children) =>
    let cx : LiftLowerContext (core3 grow) :=
      { opts := { memory := some source.memory, encoding := source.encoding }, inst := source.inst }
    let (after, result) := runLocal
      (OwnedMemory.buildNode sig Component.Limits.spec Quirks.none cx source.tag (.flat payload) children) state.reference
    (after, (result.mapError .localEffect).bind fun lifted => lifted.mapError (Issue.claims ∘ Claims.Issue.lift))

/-- Receipt-aware atomic `accept-node`. A load trap preserves canonical table effects,
but no rejected call can publish a tree or either class of claim. -/
def attempt (contract : Contract sig) (memory : Option Nat) (state : World grow sig)
    (call : UCall Nat) : World grow sig × Except Issue (BitVec 32) :=
  let (reference, result) := load contract memory state call
  match result.bind (fun tree => (state.writer.register tree).mapError .claims) with
  | .error issue => ({ state with reference }, .error issue)
  | .ok writer => (⟨reference, writer⟩, .ok (BitVec.ofNat 32 writer.accepted.length))

/-- Keep the typed diagnostic at the host boundary. The synchronous Core import ABI
returns a handle or traps the current invocation; it does not undo the guest's writes. -/
def answer (contract : Contract sig) (memory : Option Nat) (state : World grow sig)
    (call : UCall Nat) (reply : UReply) (updated : World grow sig) : Prop :=
  let (next, result) := attempt contract memory state call
  updated = next ∧ reply = ⟨call.store, match result with
    | .ok handle => .values [.num ⟨.int .i32, handle⟩]
    | .error _ => .trap⟩

def env (contract : Contract sig) (grow : SingleThreaded.GrowOracle) (memory : Option Nat) : SEnv UImp :=
  ⟨World grow sig, answer contract memory, fun _ _ => False⟩

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core
