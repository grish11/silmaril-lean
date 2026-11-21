module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.PublicCollection.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PublicCollection

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.PublicCollection

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open PayloadPrefix (CollectionTailAt)

/-- Both parked public give routes reach the actual dynamic collection allocator
or stop before allocation. On a classified callback path, the return comparison
uses reached memory bounds and rechecks live claims before the child traversal. -/
theorem Site.parked {grow : Silmaril.Wasm.SingleThreaded.GrowOracle} {sig : Signature}
    (site : Site grow sig) (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (next : site.ReferenceNext) (linked : site.Linked bindings) :
    Outcome site profile ready bindings next (site.TailRule profile ready bindings) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PublicCollection.parked site profile ready bindings next linked
    (fun _ _ => id)

/-- For a dynamic list of handles, the placed children need no additional
comparison premise. The actual leaf programs can still refuse or trap. -/
theorem Site.parked_handles {grow : Silmaril.Wasm.SingleThreaded.GrowOracle} {sig : Signature}
    (site : Site grow sig) (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (next : site.ReferenceNext) (linked : site.Linked bindings)
    (handles : ∀ item ∈ site.entries, CanonicalHandle item) : Outcome site profile ready bindings next (fun _ _ => True) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PublicCollection.parked site profile ready bindings next linked
    (fun reached pointer _ reference bytes _ _ => CollectionTailAt.of_children site.destination site.inst site.entries site.area
      site.route.output 0 pointer bytes reached reference
      (fun item member address pos => PayloadPrefix.memory_handle site.destination site.inst item pos address (handles item member)))

/-- Both public give routes compare an entire compiled non-string scalar
list after a classified allocator return, with no separate child premise.
This reaches the reply continuation, not delivery of the reply. -/
theorem Site.parked_scalars {grow : Silmaril.Wasm.SingleThreaded.GrowOracle} {sig : Signature}
    (site : Site grow sig) (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (next : site.ReferenceNext) (linked : site.Linked bindings)
    (primitive : WIT.Primitive) (element : site.element = .prim primitive) (nonString : primitive ≠ .string) :
    Outcome site profile ready bindings next (fun _ _ => True) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PublicCollection.parkedScalars
    site profile ready bindings next linked primitive element nonString

/-- Compare both parked public gives for lists of recursively nested local
records/tuples (or flat maps in value-entry mode). The compiled layout supplies
each reached placement; live guards and canonical traps still stop the
prefix with its earlier effects. The outer allocator path is classified as
in `Outcome`; this does not cover allocators inside entries. -/
theorem Site.parked_local_entries {grow : Silmaril.Wasm.SingleThreaded.GrowOracle} {sig : Signature}
    (site : Site grow sig) (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (next : site.ReferenceNext) (linked : site.Linked bindings)
    (fragment : ∀ item ∈ site.entries, PayloadPrefix.LocalMemory item) : Outcome site profile ready bindings next (fun _ _ => True) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PublicCollection.parkedLocalEntries
    site profile ready bindings next linked fragment

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.PublicCollection
