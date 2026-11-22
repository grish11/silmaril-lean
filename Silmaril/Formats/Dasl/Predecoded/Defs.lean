module

public import Silmaril.Formats.Dasl.Wire.Defs
public import Silmaril.Semantics.Naming.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl.Predecoded

open Silmaril.Semantics.Naming

/-- Pointwise witness for an object-only byte lookup and its separately built value lookup.
Neither the byte bindings nor the choice of object names are asserted to have hash integrity. -/
def Agrees {Name : Type} (wire : Name → Option ByteArray)
    (decoded : Name → Option (Shallow Wire.Cid)) : Prop :=
  ∀ name, decoded name = (wire name).bind Wire.parse?

end Silmaril.Formats.Dasl.Predecoded
