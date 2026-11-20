module

public import Silmaril.Formats.Dasl.Mst.Route.Defs
import Silmaril.Proofs.Formats.Dasl.MstRoute

public section

namespace Silmaril.Formats.Dasl.Mst

open Silmaril.Semantics.Naming

variable {Name : Type}

theorem Node.slots_separated {ctx : Context} {layerOf : Key → Nat} {node : Node Name}
    (valid : ctx.Valid layerOf node) :
    (node.slots ctx).Pairwise (fun left right => ∀ key, left.Covers key → ¬ right.Covers key) :=
  Proofs.Formats.Dasl.MstRoute.slots_separated _ _ _ valid.1

theorem Realizes.mono {layerOf : Key → Nat} {source extension : Relation Name (Node Name)}
    {expected : Option Context} {name : Name} {entries : List (Key × Name)}
    (tree : Realizes layerOf source expected name entries) (incl : Subset source extension) :
    Realizes layerOf extension expected name entries :=
  Proofs.Formats.Dasl.MstRoute.realizes_mono incl tree

theorem Realizes.ordered {layerOf : Key → Nat} {reference : Relation Name (Node Name)}
    {expected : Option Context} {name : Name} {entries : List (Key × Name)}
    (tree : Realizes layerOf reference expected name entries) :
    entries.Pairwise (fun left right => left.1.before right.1) :=
  Proofs.Formats.Dasl.MstRoute.realizes_ordered tree

theorem route_sound {layerOf : Key → Nat} {reference : Relation Name (Node Name)} (bound : Binding reference)
    {read : Name → Wire.ReadResult (Shallow Name)} (sound : ReadSound read reference)
    {expected : Option Context} {name : Name} {entries : List (Key × Name)}
    (tree : Realizes layerOf reference expected name entries) {fuel : Nat} {key : Key} {result : Option Name}
    (checked : route layerOf read key fuel expected name = .ok result) : entries.lookup key = result :=
  Proofs.Formats.Dasl.MstRoute.route_sound bound sound tree checked

/-- A result agrees with every binding shallow-object extension containing
both the rooted representation and the successful shallow reads. Only the
selected named child is requested; a read failure there is never absence. -/
theorem route_extension_sound {layerOf : Key → Nat} {reference : Relation Name (Node Name)}
    {objects : Relation Name (Shallow Name)} (bound : Binding objects) (includes : Subset reference (nodes objects))
    {read : Name → Wire.ReadResult (Shallow Name)}
    (sound : ∀ ⦃name value⦄, read name = .found value → objects name value)
    {root : Name} {entries : List (Key × Name)} (tree : Realizes layerOf reference none root entries)
    {fuel : Nat} {key : Key} {result : Option Name}
    (checked : route layerOf read key fuel none root = .ok result) : entries.lookup key = result :=
  route_sound (nodes_binding bound) (fun {_ _ _} found parsed => ⟨_, sound found, parsed⟩) (tree.mono includes) checked

end Silmaril.Formats.Dasl.Mst
