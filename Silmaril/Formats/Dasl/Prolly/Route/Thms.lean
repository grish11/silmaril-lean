module

public import Silmaril.Formats.Dasl.Prolly.Route.Defs
public import Silmaril.Formats.Dasl.Prolly.Scan.Thms
public import Silmaril.Semantics.Prolly.Routing.Thms
import Silmaril.Proofs.Formats.Dasl.ProllyRoute

public section

namespace Silmaril.Formats.Dasl.Prolly

open Silmaril.Semantics (OrderedMap)
open Silmaril.Semantics.Prolly (Block Policy build build_entries build_routable)

variable {Name Key Payload : Type} [LinearOrder Key]

/-- A routed answer is correct against every binding reference containing the
rooted representation and the successful observations. Unvisited siblings need
not be readable, but their separators must be justified by that representation. -/
theorem routedLookup_sound {codec : Encode.PartialCodec (Block Name Key Payload) (Shallow Name)}
    {tree : Semantics.Prolly.Tree Key Payload} (routable : tree.Routable) {address : Block Name Key Payload → Name}
    {store : Store Name} (stored : Stored codec address tree store) (bound : store.Binding)
    {read : Read Name} (sound : Read.Sound read store) {width fuel : Nat} {key : Key} {result : Option Payload}
    (checked : routedLookup codec read width fuel (tree.rootName address) key = .ok result) :
    tree.entries.lookup key = result :=
  Proofs.Formats.Dasl.ProllyRoute.routedLookup_sound routable stored bound sound checked

/-- Readers may observe only part of the store. Each binding extension must
contain those successful observations and the given fully stored reference. -/
theorem routedLookup_build_sound {codec : Encode.PartialCodec (Block Name Key Payload) (Shallow Name)}
    (policy : Policy Key) {map : OrderedMap Key Payload} {address : Block Name Key Payload → Name}
    {store observed extension : Store Name} (stored : Stored codec address (build policy map) store)
    (includesTree : store.Subset extension) (includesReads : observed.Subset extension) (bound : extension.Binding)
    {read : Read Name} (sound : Read.Sound read observed) {fuel : Nat} {key : Key} {result : Option Payload}
    (checked : routedLookup codec read policy.width fuel ((build policy map).rootName address) key = .ok result) :
    map.lookup? key = result := by
  have exactResult := routedLookup_sound (build_routable policy map) (stored.mono includesTree) bound (sound.mono includesReads) checked
  simpa [OrderedMap.lookup?, build_entries] using exactResult

end Silmaril.Formats.Dasl.Prolly
