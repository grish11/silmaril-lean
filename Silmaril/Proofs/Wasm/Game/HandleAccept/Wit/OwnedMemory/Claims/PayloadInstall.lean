module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadInstall.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadGrowth.Thms
import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadInstall

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled

variable {grow : SingleThreaded.GrowOracle} {sig : Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Signature}

theorem call_growing (bindings : List (Binding sig)) (ready : HostReady (HostState sig))
    {call : Call (core3 grow)} (linked : LinkedPayloadCall bindings call) :
    CoreGrowing (specDispatch ready (host bindings) call) := by
  cases linked with
  | allocator kind => exact allocator_dispatch_growing ready _ kind
  | give name type args inst destination schema resolved =>
    exact linked_give_dispatch_growing bindings ready name type args inst destination schema resolved

theorem install (bindings : List (Binding sig)) (ready : HostReady (HostState sig))
    (reached : Machine.Config (core3 grow) (HostState sig)) (label : Label (core3 grow) (HostState sig))
    (linked : LinkedPayloadInstall bindings reached label) :
    CoreGrowthInstall (specDispatch ready (host bindings)) reached label := by
  cases label with
  | host event => cases event <;> first | exact False.elim linked | trivial
  | tau =>
    cases control : reached.ctl with
    | nil => simp only [CoreGrowthInstall, control]
    | cons active rest =>
      rcases active with ⟨thread, focus, segments⟩
      cases focus with
      | prog program =>
        cases program with
        | pure => simp only [CoreGrowthInstall, control]
        | op operation next =>
          cases operation <;> simp only [CoreGrowthInstall, LinkedPayloadInstall, control] at linked ⊢
          all_goals exact call_growing bindings ready linked
      | core core next =>
        cases status : (core3 grow).status reached.store.core core <;>
          simp only [CoreGrowthInstall, LinkedPayloadInstall, control, status] at linked ⊢
        exact call_growing bindings ready linked
  | _ => trivial

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadInstall
