module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadLeaf.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.CanonicalTree.Defs
public import Silmaril.Wasm.Component.Reference.Machine.Step.Defs
public import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadLeaf

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine Silmaril.Wasm.Execution.Core
open Stored.Endpoints.RecordLower (Field)

theorem liveLeafPlan_spend_live {grow : SingleThreaded.GrowOracle} {sig : Signature}
    {store : CStore (core3 grow)} {state : State sig} {index : Nat} {item : Field} {update : Spend}
    (planned : liveLeafPlan store state index item = .ok (some update)) : update.Live state :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadLeaf.plan_spend_live planned

/-- At a reached checked handle leaf, a failed live check stops before its
canonical operation. A successful exclusive check spends exactly its own
claim, then enters the identical reference leaf program. The scheduler runs
these reads and spends before any canonical leaf effect, even if that leaf
later traps. A shared context can proceed without a spend. These local edits
preserve active and saved coordinates even when the verdict is a typed refusal. -/
theorem RecordDestination.checked_leaf_prefix {grow : SingleThreaded.GrowOracle} {sig : Signature}
    {profile : ProfileKind} {ready : HostReady (HostState sig)}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    (reached : Machine.Config (core3 grow) (HostState sig)) (destination : RecordDestination)
    (inst : InstId) (item : Field) (index : Nat) (output : Lower.Output)
    (finish : Except Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    {thread segments rest}
    (focused : reached.ctl = ⟨thread, .prog (Record.Effects.checkedLeaf recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width item index output >>= finish), segments⟩ :: rest) :
    let canonical := Endpoints.RecordLower.CanonicalTree.leaf Limits.spec Quirks.none (destination.context inst)
      destination.width item output >>= fun result => finish (.ok result)
    let (postHost, next) := match liveLeafPlan reached.store reached.host.writer index item with
      | .error issue => (reached.host, finish (.error issue))
      | .ok none => (reached.host, canonical)
      | .ok (some spend) => ({ reached.host with writer := spend.apply reached.host.writer }, canonical)
    let committed := (liveLeafPlan reached.store reached.host.writer index item).toOption.join
    ∃ labels, (∀ label ∈ labels, label = .tau) ∧ LeafGuardSteps profile ready dispatch reached labels
      { reached with host := postHost, ctl := ⟨thread, .prog next, segments⟩ :: rest } committed :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadLeaf.leaf_prefix
    reached destination inst item index output finish focused

theorem LeafGuardSteps.tracks {grow : SingleThreaded.GrowOracle} {sig : Signature}
    {profile : ProfileKind} {ready : HostReady (HostState sig)}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {before after labels spend} (run : LeafGuardSteps profile ready dispatch before labels after spend)
    (place : ReturnFrame.Occurrence.Location) : ReturnFrame.Occurrence.Prefix profile ready dispatch before place labels after place :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadLeaf.guard_tracks run place

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
