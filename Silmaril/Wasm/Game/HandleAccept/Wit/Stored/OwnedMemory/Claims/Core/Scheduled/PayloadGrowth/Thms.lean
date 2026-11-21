module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Defs
public import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Defs
import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PublicEmitterGrowth

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine Silmaril.Wasm.Execution.Core

variable {grow : SingleThreaded.GrowOracle} {sig : Signature}

theorem givePayload_coreGrowing (inst : InstId) (destination : RecordDestination) (args : List FlatValue) :
    CoreGrowing (givePayload (grow := grow) (sig := sig) inst destination args) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PublicEmitterGrowth.give_payload inst destination args

theorem giveFlat_coreGrowing (inst : InstId) (destination : RecordDestination) (payload : Stored.TypeOf)
    (args : List FlatValue) : CoreGrowing (giveFlat (grow := grow) (sig := sig) inst destination payload args) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PublicEmitterGrowth.give_flat inst destination payload args

theorem linked_give_dispatch_growing (bindings : List (Binding sig)) (ready : HostReady (HostState sig))
    (name : String) (type : V1.FuncType) (args : List FlatValue)
    (inst : InstId) (destination : RecordDestination) (schema : Option Stored.TypeOf)
    (linked : resolveBinding bindings name type = .ok ⟨name, inst,
      schema.elim (.givePayload destination) (.giveFlat destination)⟩) :
    CoreGrowing (specDispatch ready (host (grow := grow) bindings) (.hostCallout (.embedder name type) args)) :=
  embedder_dispatch_growing ready _ name type args
    (Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PublicEmitterGrowth.dispatch_give
      bindings name type args inst destination schema linked)

/-- A reached callout to either public payload binding installs a certified
program. This includes admission, selection, the recursive emitter and reply
journaling. It also covers the closed window via the actual entry and confinement
rules. Further late-bound calls retain their own installation obligations. -/
theorem parked_give_coreGrowthInstall (bindings : List (Binding sig)) (ready : HostReady (HostState sig))
    (name : String) (type : V1.FuncType) (args : List FlatValue)
    (inst : InstId) (destination : RecordDestination) (schema : Option Stored.TypeOf)
    (start : Machine.Config (core3 grow) (HostState sig)) {thread core continuation segments rest}
    (parked : start.ctl = ⟨thread, .core core continuation, segments⟩ :: rest)
    (calling : (core3 grow).status start.store.core core = .callout (.embedder name type) args)
    (linked : resolveBinding bindings name type = .ok ⟨name, inst,
      schema.elim (.givePayload destination) (.giveFlat destination)⟩) :
    CoreGrowthInstall (specDispatch ready (host (grow := grow) bindings)) start .tau := by
  simp only [CoreGrowthInstall, parked, calling]
  exact linked_give_dispatch_growing bindings ready name type args inst destination schema linked

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
