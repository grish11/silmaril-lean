module

public import Silmaril.Formats.Dasl.StringObjectMap.Index.Defs
public import Silmaril.Formats.Dasl.StringObjectMap.Thms
import Silmaril.Proofs.Formats.Dasl.StringObjectMapIndex

public section

namespace Silmaril.Formats.Dasl.StringObjectMap.Index

open Silmaril.Semantics.Prolly (Policy)

/-- For a stored canonical index and binding reference, success gives either
closed-view absence or a sound shallow value read. No digest or name uniqueness is assumed. -/
theorem lookup_sound {Name : Type} (policy : Policy String)
    {layout : Layout Name} {address : Block Name → Name} {store : Store Name}
    (stored : Prolly.Stored blockCodec address (build policy layout) store)
    (bound : store.Binding) {read : Read Name} (sound : Read.Sound read store)
    {fuel : Nat} {key : String} {value : Option (Shallow Name)}
    (checked : lookup read policy.width fuel ((build policy layout).rootName address) key = .ok value) :
    LookupSpec store (layout.lookup? key) value :=
  Proofs.Formats.Dasl.StringObjectMapIndex.lookup_sound policy stored bound sound checked

end Silmaril.Formats.Dasl.StringObjectMap.Index
