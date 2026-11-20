module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Defs
public import Silmaril.Wasm.Component.Reference.Machine.Step.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Execution.Core

variable {sig : Signature} {grow : SingleThreaded.GrowOracle}

/-- The actual machine step that registered a tree and journaled its handle, within a
longer run. This does not require a Core return or delivery of a waitable event. -/
def PublicationCut {prof : ProfileKind} {ready : HostReady (HostState sig)}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    (initial : Config (core3 grow) (HostState sig)) (labels : List (Label (core3 grow) (HostState sig)))
    (final : Config (core3 grow) (HostState sig)) (handle : BitVec 32) (tree : OwnedMemory.Tree sig) : Prop :=
  ∃ earlier label suffix before after ticket,
    labels = earlier ++ label :: suffix ∧
    Steps prof ready dispatch initial earlier before ∧
    Step prof ready dispatch before label after ∧
    Steps prof ready dispatch after suffix final ∧
    handle.toNat = before.host.writer.accepted.length + 1 ∧
    before.host.writer.register tree = .ok after.host.writer ∧
    after.host.publications = before.host.publications ++ [(ticket, handle.toNat)]

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
