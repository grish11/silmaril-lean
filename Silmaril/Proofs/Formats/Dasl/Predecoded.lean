module

public import Silmaril.Formats.Dasl.Predecoded.Defs

public section

namespace Silmaril.Proofs.Formats.Dasl.Predecoded

open Silmaril.Formats.Dasl Silmaril.Semantics.Naming

theorem lookup_iff {Name : Type} {wire : Name → Option ByteArray}
    {decoded : Name → Option (Shallow Wire.Cid)} (witness : Predecoded.Agrees wire decoded)
    {name : Name} {value : Shallow Wire.Cid} :
    graph decoded name value ↔ ∃ bytes, graph wire name bytes ∧ Wire.parse? bytes = some value := by
  change decoded name = some value ↔ _
  rw [witness name]
  exact Option.bind_eq_some_iff

end Silmaril.Proofs.Formats.Dasl.Predecoded
