module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence.Public.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PublicMemorySequence

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Stored.Endpoints.RecordLower

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {pointer : FlatValue}
  {profile : ProfileKind} {ready : HostReady (HostState sig)} {bindings : List (Binding sig)}

/-- Compare the actual parked public `givePayload` body for arbitrary
record and tuple nesting with interleaved strings and checked handles.
The public guards provide root placement and string fit; descendants use
compiled offsets and the live writer reached after earlier callbacks. -/
theorem parked_givePayload (call : PayloadRoot.Site grow sig (.memory pointer)) (linked : call.Linked bindings)
    (depth : Nat) (next : call.ReferenceNext) (shape : ParkedShape depth call.field)
    {addr : Nat} (realloc : call.destination.realloc = some addr) :
    PayloadRoot.Cut call profile ready bindings (ParkedBody call depth next profile ready bindings) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PublicMemorySequence.parked call linked depth next shape realloc

/-- Both actual parked give bindings compare a compiled list root with
arbitrarily many nested record/tuple entries containing allocating strings
and handles. Its independently reached recheck can refuse before entries;
the descriptor and original reply run only after their respective guards. -/
theorem parked_list {route : GiveEffectRoute} (call : PayloadRoot.Site grow sig route) (linked : call.Linked bindings)
    (element : TypeOf) (entries : List Field) (depth : Nat) (next : call.ReferenceNext)
    (compiledList : call.field = .dynamic (.list element) element entries)
    (shapes : ∀ item ∈ entries, ParkedShape depth item) {addr : Nat} (realloc : call.destination.realloc = some addr) :
    PayloadRoot.Cut call profile ready bindings (ParkedListBody call element entries depth next profile ready bindings) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PublicMemorySequence.parkedList
    call linked element entries depth next compiledList shapes realloc

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence
