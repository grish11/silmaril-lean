module

public import Silmaril.Formats.Dasl.Mst.Build.Defs
import Silmaril.Proofs.Formats.Dasl.MstBuild

public section

namespace Silmaril.Formats.Dasl.Mst

open Silmaril.Semantics.Naming (Relation Subset)

variable {Name : Type}

theorem split_flatten (layerOf : Key → Nat) (layer : Nat) (records : List (Record Name)) :
    (splitLayer layerOf layer records).flatten = records :=
  Proofs.Formats.Dasl.MstBuild.split_flatten layerOf layer records

theorem split_pivots (layerOf : Key → Nat) (layer : Nat) (records : List (Record Name)) :
    (splitLayer layerOf layer records).pivots.map Prod.fst = records.filter (fun record => layerOf record.1 == layer) :=
  Proofs.Formats.Dasl.MstBuild.split_pivots layerOf layer records

/-- A successful construction realizes exactly the input entries in any
relation that includes its trace. Binding is not needed until the relation
is used for deterministic CAS lookup. -/
theorem build_realizes {layerOf : Key → Nat} {nameNode : Node Name → Option Name}
    {reference : Relation Name (Node Name)} {records : List (Record Name)} {built : Built Name}
    (hit : build layerOf nameNode records = some built) (included : Subset built.observed reference) :
    Realizes layerOf reference none built.root records :=
  Proofs.Formats.Dasl.MstBuild.build_realizes hit included

/-- Before raw admission the trace is included in the naming graph, not
necessarily binding. Bottom-up name determinism does not rule out collisions. -/
theorem build_names {layerOf : Key → Nat} {nameNode : Node Name → Option Name}
    {records : List (Record Name)} {built : Built Name} (hit : build layerOf nameNode records = some built) :
    Subset built.observed (fun name node => nameNode node = some name) :=
  Proofs.Formats.Dasl.MstBuild.build_names hit

theorem build_total {layerOf : Key → Nat} {nameNode : Node Name → Option Name}
    (total : ∀ node, ∃ name, nameNode node = some name) {records : List (Record Name)}
    (ordered : OrderedRecords records) : ∃ built, build layerOf nameNode records = some built :=
  Proofs.Formats.Dasl.MstBuild.build_total total ordered

theorem Atproto.build_realizes {nameNode : Node Name → Option Name} {reference : Relation Name (Node Name)}
    {records : List (Record Name)} {built : Built Name} (hit : Atproto.build nameNode records = some built)
    (included : Subset built.observed reference) : Realizes keyLayer reference none built.root records :=
  Mst.build_realizes hit included

end Silmaril.Formats.Dasl.Mst
