module

public import Silmaril.Formats.Dasl.Encode.ClassMap.Defs
public import Silmaril.Formats.Dasl.Encode.Collection.Thms
public import Silmaril.Formats.PER.ClassMap.Thms

public section

namespace Silmaril.Formats.Dasl.Encode

open Silmaril.Semantics

variable {Key Class Ref Name Repr : Type} [LinearOrder Key]

theorem classMap_representable_iff (key : TotalCodec Key (Tree Ref Name)) (label : TotalCodec Class (Tree Ref Name))
    (lookup : PER.ClassMap Key Class) :
    (∃ repr, RepresentsMap (classMap key label) repr lookup) ↔ (OrderedMap.support lookup).Finite :=
  representsMap_iff_finite _ lookup

theorem classMapFibers_recover? (codec : PartialCodec (OrderedMap Key Class) Repr)
    {labels : OrderedMap Key Class} {repr : Repr} (encoded : codec.encode? labels = some repr) :
    classMapFibers? codec repr = some (PER.fibers labels.lookup?) := by
  simp [classMapFibers?, codec.recovers encoded]

theorem classMapFibers_recover (key : TotalCodec Key (Tree Ref Name)) (label : TotalCodec Class (Tree Ref Name))
    (labels : OrderedMap Key Class) :
    classMapFibers? (classMap key label).partial ((classMap key label).encode labels) =
      some (PER.fibers labels.lookup?) := classMapFibers_recover? _ rfl

theorem classMapWireFibers_recover (profile : Wire.Profile Name) (key : TotalCodec Key (Shallow Name))
    (label : TotalCodec Class (Shallow Name)) [DecidableEq (OrderedMap Key Class)]
    {labels : OrderedMap Key Class} {bytes : ByteArray}
    (encoded : (classMapWireCodec profile key label).encode? labels = some bytes) :
    classMapWireFibers? profile key label bytes = some (PER.fibers labels.lookup?) :=
  classMapFibers_recover? _ encoded

end Silmaril.Formats.Dasl.Encode
