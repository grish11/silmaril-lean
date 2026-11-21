module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadEffects.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled

open Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Execution.Core
open Stored.Endpoints.RecordLower (Field)

/-- An exclusive leaf schedules precisely one spend after its live check.
An error context checks the reached arena without spending anything. -/
def liveLeafPlan {sig : Signature} {grow : SingleThreaded.GrowOracle}
    (store : CStore (core3 grow)) (state : State sig) (index : Nat) :
    Field → Except Endpoints.RecordLower.Issue (Option Spend)
  | .owner receipt => (Record.prepareOwner state receipt).map (fun _ => some (.owner (receiptId receipt)))
      |>.mapError (.nested index)
  | .endpoint channel element id => (Record.prepareEndpoint store state channel element id).map
      (fun _ => some (.endpoint id)) |>.mapError (.nested index)
  | .context id =>
    if (store.errCtx? id).isNone then .error (.field index (.beforeAllocation .missingContext)) else .ok none
  | _ => .ok none

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
