module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record.Defs

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.RecordTransfer

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Value
open Silmaril.Wasm.Game.HandleAccept.Wit
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Lower (Output)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower (Issue)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower.Internal (runField publishSlot)

private theorem prepareOwner_rep {sig : Signature} {state next : Claims.State sig} {receipt : Receipt} {rep : Nat}
    (checked : prepareOwner state receipt = .ok (rep, next)) : rep = receipt.2.representation := by
  simp only [prepareOwner, bind, Except.bind, Except.mapError] at checked
  split at checked
  · contradiction
  · rename_i prepared found
    split at checked
    · contradiction
    · rename_i compatible
      change Except.ok (prepared.1, prepared.2) = .ok (rep, next) at checked
      have eq := congrArg Prod.fst (Except.ok.inj checked)
      exact eq.symm.trans (by simpa using compatible)

theorem owner {E : CoreEngine} {World : Type} {sig : Signature} (access : Record.Access E World sig)
    (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (width : AddrType) (receipt : Receipt) (index : Nat) (output : Output) :
    runField limits quirks cx (authority access limits cx) width (.owner receipt) index output = (
      let canonical := Output.rec (motive := fun out => P E World out.Result)
        (fun ptr => store limits quirks cx (.own receipt.2.representation) (.own receipt.1) ptr)
        (lowerFlatAt limits quirks cx width (.own receipt.2.representation) (.own receipt.1)) output
      do
        match prepareOwner (← access.read) receipt with
        | .error issue => pure (.error (.nested index issue))
        | .ok _ =>
          access.spendOwner (receiptId receipt)
          return .ok (← canonical)) := by
  cases output <;> simp only [runField, authority, commitOwner, publishSlot]
  all_goals
    dsimp only [Output.Result]
    first | rw [lowerFlatAt] | rw [store]
    simp only [Prog.bind_eq, Prog.bind_assoc]
    congr 1
    funext state
    cases checked : prepareOwner state receipt with
    | error => rfl
    | ok pair =>
      obtain ⟨representation, next⟩ := pair
      simp only [prepareOwner_rep checked, Prog.bind_assoc, Prog.pure_eq, Prog.pure_bind']

theorem endpoint {E : CoreEngine} {World : Type} {sig : Signature} (access : Record.Access E World sig)
    (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (width : AddrType) (channel : Async.Channel) (element : Async.Element) (id : EndId)
    (index : Nat) (output : Output) :
    let type := ListLower.endpointType channel element
    let value : Val := match channel with | .stream => .stream id | .future => .future id
    runField limits quirks cx (authority access limits cx) width (.endpoint channel element id) index output = (
      let canonical := Output.rec (motive := fun out => P E World out.Result)
        (fun ptr => store limits quirks cx value type ptr)
        (lowerFlatAt limits quirks cx width value type) output
      do
        let state ← access.read
        match prepareEndpoint (← getStore) state channel element id with
        | .error issue => pure (.error (.nested index issue))
        | .ok _ =>
          access.spendEndpoint id
          return .ok (← canonical)) := by
  cases channel <;> cases output <;>
    simp [runField, authority, publishSlot, ListLower.endpointType,
      lowerFlatAt, store, lowerStream, lowerFuture, Async.Channel.endKind]
  all_goals
    dsimp only [Output.Result]
    simp only [Prog.bind_assoc]
    congr 1
    funext state
    congr 1
    funext reached
    cases prepareEndpoint reached state _ _ id <;> simp [Prog.bind_assoc]

theorem context {E : CoreEngine} {World : Type} {sig : Signature} (access : Record.Access E World sig)
    (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (width : AddrType) (id : ErrCtxId) (index : Nat) (output : Output) :
    runField limits quirks cx (authority access limits cx) width (.context id) index output = (
      let canonical := Output.rec (motive := fun out => P E World out.Result)
        (fun ptr => store limits quirks cx (.errorContext id) .errorContext ptr)
        (lowerFlatAt limits quirks cx width (.errorContext id) .errorContext) output
      do
        let _ ← access.read
        if ((← getStore).errCtx? id).isNone then
          return .error (.field index (.beforeAllocation .missingContext))
        return .ok (← canonical)) := by
  cases output <;> simp [runField, authority, publishSlot, lowerFlatAt, store]
  all_goals
    dsimp only [Output.Result]
    simp only [Prog.bind_assoc]
    congr 1
    funext state
    congr 1
    funext reached
    split <;> simp [Prog.bind_assoc]

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.RecordTransfer
