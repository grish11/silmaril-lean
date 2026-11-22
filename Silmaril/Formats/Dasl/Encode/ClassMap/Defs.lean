module

public import Silmaril.Formats.Dasl.Encode.Collection.Defs
public import Silmaril.Formats.Dasl.Wire.Profile.Defs
public import Silmaril.Formats.PER.ClassMap.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl.Encode

open Silmaril.Semantics

variable {Key Class Ref Name Repr : Type} [LinearOrder Key]

/-- Encode a finite class assignment with separate key and class codecs.
Only keys are ordered. The output preserves labels, not just their fibers. -/
abbrev classMap (key : TotalCodec Key (Tree Ref Name)) (label : TotalCodec Class (Tree Ref Name)) :
    TotalCodec (OrderedMap Key Class) (Tree Ref Name) := pairMap key label

/-- Missing or invalid encodings are not decoded as an empty partition. -/
def classMapFibers? (codec : PartialCodec (OrderedMap Key Class) Repr) (repr : Repr) : Option (PER Key) :=
  (codec.decode? repr).map fun labels => PER.fibers labels.lookup?

abbrev classMapWireCodec (profile : Wire.Profile Name) (key : TotalCodec Key (Shallow Name))
    (label : TotalCodec Class (Shallow Name)) [DecidableEq (OrderedMap Key Class)] :
    PartialCodec (OrderedMap Key Class) ByteArray := profile.codec (classMap key label)

/-- Wire reads do not need equality of labels. The existing partial writer
adds decidable equality of the finite map only for its recovery check. -/
def classMapWireFibers? (profile : Wire.Profile Name) (key : TotalCodec Key (Shallow Name))
    (label : TotalCodec Class (Shallow Name)) (bytes : ByteArray) : Option (PER Key) :=
  (profile.decode? (classMap key label) bytes).map fun labels => PER.fibers labels.lookup?

end Silmaril.Formats.Dasl.Encode
