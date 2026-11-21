module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Defs
public import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine Silmaril.Wasm.Execution.Core

variable {grow : SingleThreaded.GrowOracle} {sig : Signature}

/-- The allocator protocol and calls which actually resolve to a linked give
binding. A closed-window invocation is included; admission still runs. -/
inductive LinkedPayloadCall (bindings : List (Binding sig)) : Call (core3 grow) → Prop where
  | allocator {call} : AllocatorCall call → LinkedPayloadCall bindings call
  | give (name : String) (type : V1.FuncType) (args : List FlatValue) (inst : InstId)
      (destination : RecordDestination) (schema : Option Stored.TypeOf) :
      resolveBinding bindings name type = .ok ⟨name, inst,
        schema.elim (.givePayload destination) (.giveFlat destination)⟩ →
      LinkedPayloadCall bindings (.hostCallout (.embedder name type) args)

/-- This tests actual install sites, not the bodies of callbacks or saved
continuations. Other Core computation, including byte writes, is unrestricted.
An arbitrary host `run` and unrecognized dispatcher calls are not included. -/
def LinkedPayloadInstall (bindings : List (Binding sig)) (reached : Machine.Config (core3 grow) (HostState sig))
    (label : Label (core3 grow) (HostState sig)) : Prop :=
  match label with
  | .host (.run _) => False
  | .tau =>
    match reached.ctl with
    | ⟨_, .prog (.op (.call call) _), _⟩ :: _ => LinkedPayloadCall bindings call
    | ⟨_, .prog (.op (.newThread body) _), _⟩ :: _ => LinkedPayloadCall bindings (.threadBody body)
    | ⟨_, .core core _, _⟩ :: _ =>
      match (core3 grow).status reached.store.core core with
      | .callout host args => LinkedPayloadCall bindings (.hostCallout host args)
      | _ => True
    | _ => True
  | _ => True

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
