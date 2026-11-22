module

public import Silmaril.Formats.Dasl.Predecoded.Defs
import Silmaril.Proofs.Formats.Dasl.Predecoded

public section

namespace Silmaril.Formats.Dasl.Predecoded

open Silmaril.Semantics.Naming

theorem lookup_iff {Name : Type} {wire : Name → Option ByteArray}
    {decoded : Name → Option (Shallow Wire.Cid)} (witness : Agrees wire decoded)
    {name : Name} {value : Shallow Wire.Cid} :
    graph decoded name value ↔ ∃ bytes, graph wire name bytes ∧ Wire.parse? bytes = some value :=
  Proofs.Formats.Dasl.Predecoded.lookup_iff witness

theorem lookup_of_serializes {Name : Type} {wire : Name → Option ByteArray}
    {decoded : Name → Option (Shallow Wire.Cid)} (witness : Agrees wire decoded)
    {name : Name} {value : Shallow Wire.Cid} {bytes : ByteArray}
    (bound : graph wire name bytes) (serialized : Wire.Serializes value bytes) :
    graph decoded name value :=
  (lookup_iff witness).mpr ⟨bytes, bound, serialized.2⟩

end Silmaril.Formats.Dasl.Predecoded
