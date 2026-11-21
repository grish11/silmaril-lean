module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.RecordTransfer

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Value
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)

/-- The owner leaf used by checked flat and memory lowering is the canonical program
after a live nominal check and a commitment-time spend. A failed check performs no
spend or canonical write; a later canonical trap does not undo the spend. The
representation given to the canonical program is exactly the checked receipt's. -/
theorem runField_owner_canon {E : CoreEngine} {World : Type} {sig : Signature} (access : Access E World sig)
    (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (width : AddrType) (receipt : Receipt) (index : Nat) (output : Lower.Output) :
    Endpoints.RecordLower.Internal.runField limits quirks cx (authority access limits cx)
      width (.owner receipt) index output = (
      let canonical := Lower.Output.rec (motive := fun out => P E World out.Result)
        (fun ptr => store limits quirks cx (.own receipt.2.representation) (.own receipt.1) ptr)
        (lowerFlatAt limits quirks cx width (.own receipt.2.representation) (.own receipt.1)) output
      do
        match prepareOwner (← access.read) receipt with
        | .error issue => pure (.error (.nested index issue))
        | .ok _ =>
          access.spendOwner (receiptId receipt)
          return .ok (← canonical)) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.RecordTransfer.owner
    access limits quirks cx width receipt index output

/-- Check the current claim and endpoint arena, then spend the readable endpoint
before the canonical move. A late canonical trap retains that commitment. -/
theorem runField_endpoint_canon {E : CoreEngine} {World : Type} {sig : Signature} (access : Access E World sig)
    (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (width : AddrType) (channel : Async.Channel) (element : Async.Element) (id : EndId)
    (index : Nat) (output : Lower.Output) :
    let type := Endpoints.ListLower.endpointType channel element
    let value : Val := match channel with | .stream => .stream id | .future => .future id
    Endpoints.RecordLower.Internal.runField limits quirks cx (authority access limits cx)
      width (.endpoint channel element id) index output = (
      let canonical := Lower.Output.rec (motive := fun out => P E World out.Result)
        (fun ptr => store limits quirks cx value type ptr)
        (lowerFlatAt limits quirks cx width value type) output
      do
        let state ← access.read
        match prepareEndpoint (← getStore) state channel element id with
        | .error issue => pure (.error (.nested index issue))
        | .ok _ =>
          access.spendEndpoint id
          return .ok (← canonical)) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.RecordTransfer.endpoint
    access limits quirks cx width channel element id index output

/-- Error contexts use the reached arena check but do not spend an exclusive claim. -/
theorem runField_context_canon {E : CoreEngine} {World : Type} {sig : Signature} (access : Access E World sig)
    (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (width : AddrType) (id : ErrCtxId) (index : Nat) (output : Lower.Output) :
    Endpoints.RecordLower.Internal.runField limits quirks cx (authority access limits cx)
      width (.context id) index output = (
      let canonical := Lower.Output.rec (motive := fun out => P E World out.Result)
        (fun ptr => store limits quirks cx (.errorContext id) .errorContext ptr)
        (lowerFlatAt limits quirks cx width (.errorContext id) .errorContext) output
      do
        let _ ← access.read
        if ((← getStore).errCtx? id).isNone then
          return .error (.field index (.beforeAllocation .missingContext))
        return .ok (← canonical)) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.RecordTransfer.context
    access limits quirks cx width id index output

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record
