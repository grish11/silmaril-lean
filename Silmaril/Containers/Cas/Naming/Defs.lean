module

public import Silmaril.Containers.Cas.Defs
public import Silmaril.Semantics.Naming.Defs

@[expose] public section

namespace Silmaril.Containers.Cas.Store

/-- The relational view of the existing partial map, with no new integrity assumptions.
Import this adapter explicitly to use the relational naming API. -/
def relation {D C : Type} (store : Store D C) : Semantics.Naming.Relation D C :=
  Semantics.Naming.graph store

/-- Preserve present contents without decoding or checking them before the fallback. -/
def fillMissing {D C : Type} (base defaults : Store D C) : Store D C :=
  fun name => (base name).orElse (fun _ => defaults name)

end Silmaril.Containers.Cas.Store
