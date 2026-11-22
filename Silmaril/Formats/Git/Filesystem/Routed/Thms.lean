module

public import Silmaril.Formats.Git.Filesystem.Routed.Defs
public import Silmaril.Formats.Git.Filesystem.Thms
public import Silmaril.Formats.Dasl.Arena.Prolly.Thms
import Silmaril.Proofs.Formats.Git.Filesystem.Routed

public section

namespace Silmaril.Formats.Git.Filesystem

open Silmaril.Semantics
open Formats.Dasl.Prolly (ByteKey Fault Stored Read route routedLookup_sound)
open Formats.Dasl.Arena.Prolly (Resident)

theorem checkedChild_error {store : Store} {query : Cid → ByteKey → Except (Fault Cid) (Option (Entry Cid))}
    {root : Cid} {key : ByteKey} {fault : Fault Cid} (valid : Dasl.validByteComponent key = true)
    (failed : query root key = .error fault) : checkedChild store query root key = .error (refineRead store fault) := by
  simp [checkedChild, valid, failed, Except.mapError, Bind.bind, Except.bind]

variable {hash : Hash} {store : Store} {reference : Formats.Dasl.Store Cid}
variable {directory : ShallowTree ByteKey Cid} {addressBlock : DirBlock → Cid}
variable {fuel : Nat} {key : ByteKey} {result : Option (Entry Cid)}

/-- A successful routed answer, including absence, needs a binding reference
for the entire directory, not a complete observation of every sibling. -/
theorem lookupChildRouted_sound
    (stored : Stored dirCodec addressBlock (Prolly.build policy directory.ordered) reference)
    (binding : reference.Binding) (reader : Read.Sound (dirRead hash store) reference)
    (checked : lookupChildRouted hash store fuel ((Prolly.build policy directory.ordered).rootName addressBlock) key = .ok result) :
    directory.ordered.lookup? key = result := by
  simpa only [OrderedMap.lookup?, Prolly.build_entries] using routedLookup_sound (Prolly.build_routable policy directory.ordered)
    stored binding reader (checkedChild_ok checked)

theorem lookupChildResident_sound {acquired : List Cid}
    (stored : Stored dirCodec addressBlock (Prolly.build policy directory.ordered) reference)
    (binding : reference.Binding) (reader : Read.Sound (dirRead hash store) reference)
    (checked : lookupChildResident hash store acquired fuel ((Prolly.build policy directory.ordered).rootName addressBlock) key = .ok result) :
    directory.ordered.lookup? key = result := by
  simpa only [OrderedMap.lookup?, Prolly.build_entries] using Resident.lookup_sound (Prolly.build_routable policy directory.ordered)
    stored binding reader (checkedChild_ok checked)

/-- Compare successful answers only. The routed query can succeed with a
missing unrelated sibling for which the closed scan reports a fault. -/
theorem lookupChildRouted_agrees_scan {scanned : Option (Entry Cid)}
    (stored : Stored dirCodec addressBlock (Prolly.build policy directory.ordered) reference)
    (binding : reference.Binding) (reader : Read.Sound (dirRead hash store) reference)
    (routed : lookupChildRouted hash store fuel ((Prolly.build policy directory.ordered).rootName addressBlock) key = .ok result)
    (scan : lookupChild hash store fuel ((Prolly.build policy directory.ordered).rootName addressBlock) key = .ok scanned) :
    result = scanned :=
  (lookupChildRouted_sound stored binding reader routed).symm.trans (lookupChild_sound stored binding reader scan)

theorem locateWith_agree {left right : ChildLookup}
    (agree : ∀ ⦃root key first second⦄, left root key = .ok first → right root key = .ok second → first = second)
    {root : Cid} {path : List ByteKey} {first second : Option (Entry Cid)}
    (firstOk : locateWith left root path = .ok first) (secondOk : locateWith right root path = .ok second) :
    first = second :=
  Proofs.Formats.Git.Filesystem.locateWith_agree agree firstOk secondOk

end Silmaril.Formats.Git.Filesystem
