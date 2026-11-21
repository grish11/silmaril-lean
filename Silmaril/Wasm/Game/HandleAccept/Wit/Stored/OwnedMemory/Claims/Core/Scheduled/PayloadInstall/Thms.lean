module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadInstall.Defs
import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadInstall

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine Silmaril.Wasm.Execution.Core

variable {grow : SingleThreaded.GrowOracle} {sig : Signature}

theorem LinkedPayloadInstall.growing {bindings : List (Binding sig)} (ready : HostReady (HostState sig))
    {reached : Machine.Config (core3 grow) (HostState sig)} {label : Label (core3 grow) (HostState sig)}
    (linked : LinkedPayloadInstall bindings reached label) :
    CoreGrowthInstall (specDispatch ready (host bindings)) reached label :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadInstall.install bindings ready reached label linked

/-- Certify a real prefix of the linked give/allocator dispatcher. No
per-callback proof is needed for known installs. Open calls and arbitrary host
programs still require their own certificate at the reached install site. -/
theorem linked_payload_prefix_growth {bindings : List (Binding sig)} {ready : HostReady (HostState sig)}
    {before after : Machine.Config (core3 grow) (HostState sig)} {profile : ProfileKind}
    {trace : List (Label (core3 grow) (HostState sig))}
    (run : Machine.Steps profile ready (specDispatch ready (host bindings)) before trace after)
    (growing : before.CoreGrowing)
    (installs : ∀ {reached next leading label},
      Machine.Steps profile ready (specDispatch ready (host bindings)) before leading reached →
      Step profile ready (specDispatch ready (host bindings)) reached label next →
      LinkedPayloadInstall bindings reached label ∨ CoreGrowthInstall (specDispatch ready (host bindings)) reached label) :
    CoreGrowthSteps profile ready (specDispatch ready (host bindings)) before trace after ∧ after.CoreGrowing :=
  CoreGrowthSteps.of_installs run growing fun leading step =>
    (installs leading step).elim (LinkedPayloadInstall.growing ready) id

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
