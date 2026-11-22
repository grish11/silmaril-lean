module

public import Silmaril.Semantics.Naming.Table.Defs
public import Silmaril.Semantics.Naming.Thms
import Silmaril.Proofs.Semantics.Naming.Table

public section

namespace Silmaril.Semantics.Naming.Table

variable {Name Payload : Type}

theorem lookup_iff {table : Table Payload} {route : List Bool} {payload : Payload} :
    table.lookup route = some payload ↔ Entry table route payload :=
  Proofs.Semantics.Naming.Table.lookup_iff

theorem lookup_set (table : Table Payload) (write read : List Bool) (payload : Payload) :
    (table.set write payload).lookup read =
      if read = write then some payload else table.lookup read :=
  Proofs.Semantics.Naming.Table.lookup_set table write read payload

theorem relation_binding (table : Table Payload) (route : Name → List Bool) :
    Binding (table.relation route) := by
  intro name first second left right
  exact Option.some.inj ((lookup_iff.mpr left).symm.trans (lookup_iff.mpr right))

theorem overlay_iff {left right : Name → Option Payload} (compatible : Compatible left right)
    {name : Name} {payload : Payload} :
    graph (overlay left right) name payload ↔ union (graph left) (graph right) name payload :=
  Proofs.Semantics.Naming.Table.overlay_iff compatible

theorem overlay_binding {left right : Name → Option Payload} (compatible : Compatible left right) :
    Binding (union (graph left) (graph right)) := by
  intro name first second leftEntry rightEntry
  exact graph_binding (overlay left right) ((overlay_iff compatible).mpr leftEntry)
    ((overlay_iff compatible).mpr rightEntry)

theorem overlay_namesOf {left right : Name → Option Payload} (compatible : Compatible left right)
    (payload : Payload) :
    namesOf (graph (overlay left right)) payload =
      namesOf (graph left) payload ∪ namesOf (graph right) payload :=
  Set.ext fun _ => overlay_iff compatible

end Silmaril.Semantics.Naming.Table
