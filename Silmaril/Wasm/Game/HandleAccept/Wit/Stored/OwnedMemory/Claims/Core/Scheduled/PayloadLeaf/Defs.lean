module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadEffects.Defs
public import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled

open Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Execution.Core
open Stored.Endpoints.RecordLower (Field)
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Machine ReturnFrame.Occurrence

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

/-- The checked guard reads the reached state and may finish with one concrete
claim assignment. Every proper prefix of the guard leaves the writer unchanged. -/
inductive LeafGuardSteps {sig : Signature} {grow : SingleThreaded.GrowOracle}
    (profile : ProfileKind) (ready : HostReady (HostState sig))
    (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))) :
    Config (core3 grow) (HostState sig) → List (Label (core3 grow) (HostState sig)) →
    Config (core3 grow) (HostState sig) → Option Spend → Prop where
  | done (state) : LeafGuardSteps profile ready dispatch state [] state none
  | read {before middle after labels spend}
      (step : Step profile ready dispatch before .tau middle)
      (edit : transitionEdit before .tau = .same)
      (store : middle.store = before.store) (host : middle.host = before.host)
      (tail : LeafGuardSteps profile ready dispatch middle labels after spend) :
      LeafGuardSteps profile ready dispatch before (.tau :: labels) after spend
  | commit {before spend thread frames rest next}
      (focus : before.ctl = ⟨thread,
        .prog (.op (.hostSet { before.host with writer := spend.apply before.host.writer }) next), frames⟩ :: rest) :
      LeafGuardSteps profile ready dispatch before [.tau]
        { before with
          host := { before.host with writer := spend.apply before.host.writer }
          ctl := ⟨thread, .prog (next ()), frames⟩ :: rest } (some spend)

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
