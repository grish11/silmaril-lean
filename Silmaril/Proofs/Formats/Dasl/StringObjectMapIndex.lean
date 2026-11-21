module

public import Silmaril.Formats.Dasl.Prolly.Scan.Thms
public import Silmaril.Formats.Dasl.StringObjectMap.Index.Defs
public import Silmaril.Formats.Dasl.StringObjectMap.Thms

public section

namespace Silmaril.Proofs.Formats.Dasl.StringObjectMapIndex

open Silmaril.Formats.Dasl Silmaril.Formats.Dasl.StringObjectMap
open Silmaril.Semantics.Prolly (Policy)

theorem lookup_sound {Name : Type} (policy : Policy String)
    {layout : Layout Name} {address : Index.Block Name → Name} {store : Store Name}
    (stored : Prolly.Stored Index.blockCodec address (Index.build policy layout) store)
    (bound : store.Binding) {read : Read Name} (sound : Read.Sound read store)
    {fuel : Nat} {key : String} {value : Option (Shallow Name)}
    (checked : Index.lookup read policy.width fuel ((Index.build policy layout).rootName address) key = .ok value) :
    LookupSpec store (layout.lookup? key) value := by
  unfold Index.lookup at checked
  split at checked
  next => contradiction
  next placement indexed =>
    rw [Prolly.lookup_sound policy stored bound sound indexed]
    apply recover_sound sound
    split at checked
    next => contradiction
    next recovered hit => cases checked; exact hit

end Silmaril.Proofs.Formats.Dasl.StringObjectMapIndex
