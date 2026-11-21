module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.FlatStrings.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PublicFlatStrings

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.FlatStrings

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {schema : TypeOf}
  {profile : ProfileKind} {ready : HostReady (HostState sig)} {bindings : List (Binding sig)}

/-- Compare the actual parked `giveFlat` on recursive string-bearing records,
tuples and fixed lists against `lowerFlatAt`. The linked memory check and
successful reached allocation guard supply the leaf preconditions. No
allocation-return promise or byte/claim preservation is required. -/
theorem parked_giveFlat (call : PayloadRoot.Site grow sig (.flat schema)) (linked : call.Linked bindings)
    (depth : Nat) (next : call.ReferenceNext) (shape : Shape depth call.field)
    {addr : Nat} (realloc : call.destination.realloc = some addr) :
    PayloadRoot.Cut call profile ready bindings (Body call depth next profile ready bindings) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PublicFlatStrings.parked call linked depth next shape realloc

/-- Compare the parked flat body when allocating strings and live handles are
interleaved at arbitrary record/tuple and fixed-list depth. Each handle guard
reads the reached writer, not a claim preserved by the earlier allocator. -/
theorem parked_giveFlat_mixed (call : PayloadRoot.Site grow sig (.flat schema)) (linked : call.Linked bindings)
    (depth : Nat) (next : call.ReferenceNext) (shape : MixedShape depth call.field)
    {addr : Nat} (realloc : call.destination.realloc = some addr) :
    PayloadRoot.Cut call profile ready bindings (MixedBody call depth next profile ready bindings) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PublicFlatStrings.parkedMixed call linked depth next shape realloc

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.FlatStrings
