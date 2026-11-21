module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.NestedRecord.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.NestedRecord

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.NestedRecord

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
  {ready : HostReady (HostState sig)} {bindings : List (Binding sig)}

/-- Compare a dynamic list at the current record or tuple field and resume
the actual sibling programs on a common return. The enclosing region survives
Core growth, not arbitrary byte equality. A refusal, trap, or common-frame
pop does not execute the sibling programs. -/
theorem Site.compare_at_cursor (site : Site) {origin : CStore (core3 grow)} {bytes : Nat}
    (region : site.Region origin bytes) (left right : State grow sig)
    (cursor : Cursor (E := core3 grow) (HostState sig)) (checkNext : CheckNext grow sig) (canonNext : CanonNext grow sig)
    (same : { left with ctl := right.ctl, host := right.host } = right)
    (growth : Core3.Grows origin.core right.store.core)
    (children : ∀ item ∈ site.entries, MemoryChildRule profile ready (specDispatch ready (host (grow := grow) bindings))
      site.destination site.inst item site.element)
    (following : ∀ item ∈ site.following, MemoryChildRule profile ready (specDispatch ready (host (grow := grow) bindings))
      site.destination site.inst item item.type)
    (checkAt : left.ctl = cursor.control (Record.Effects.memory recordClaims Limits.spec Quirks.none
      (site.destination.context site.inst) site.destination.width site.fields site.base site.index >>= checkNext))
    (canonAt : right.ctl = cursor.control (CanonicalTree.memory Limits.spec Quirks.none
      (site.destination.context site.inst) site.destination.width site.fields site.base >>= canonNext)) :
    site.Outcome profile ready bindings origin left right cursor checkNext canonNext :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.NestedRecord.atCursor
    site region left right cursor checkNext canonNext same growth children following checkAt canonAt

/-- Compose the dynamic list and following fields with an actual parked
`givePayload` binding. The compiled layout discharges both the list entry
and sibling comparisons for the recursively local memory fragment. -/
theorem parked_givePayload {pointer : FlatValue} (call : PayloadRoot.Site grow sig (.memory pointer))
    (linked : call.Linked bindings) (element : TypeOf) (entries following : List Field) (next : call.ReferenceNext)
    (field : call.field = .aggregate (sig.payload call.tag) (.dynamic (.list element) element entries :: following))
    (localEntries : ∀ item ∈ entries, LocalMemory item) (localTail : ∀ item ∈ following, LocalMemory item) :
    PublicOutcome call element entries following next profile ready bindings :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.NestedRecord.parked
    call linked element entries following next field localEntries localTail

/-- Compare the actual linked `giveFlat` aggregate with `lowerFlatAt`.
The allocating field returns descriptor words only on a common return;
the suffix then appends its words. Both allocator continuations retain
the reached live recheck, late traps, and enclosing issue index. -/
theorem parked_giveFlat {schema : TypeOf} (call : PayloadRoot.Site grow sig (.flat schema))
    (linked : call.Linked bindings) (element : TypeOf) (entries following : List Field) (next : call.ReferenceNext)
    (field : call.field = .aggregate (sig.payload call.tag) (.dynamic (.list element) element entries :: following))
    (localEntries : ∀ item ∈ entries, LocalMemory item) (localTail : ∀ item ∈ following, HandleShape item) :
    PublicFlatOutcome call element entries following next profile ready bindings :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.NestedRecord.parkedFlat
    call linked element entries following next field localEntries localTail

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.NestedRecord
