module

public import Silmaril.Formats.Dasl.Mst.Route.Defs
import Silmaril.Proofs.Formats.Dasl.MstRoute
import Silmaril.Proofs.Formats.Dasl.MstRouteComplete
import Silmaril.Proofs.Formats.Dasl.MstRooted

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

/-- One read per layer suffices if the reader can decode the selected path.
The soundness theorem above still applies when that path is incomplete. -/
theorem route_root_complete {layerOf : Key → Nat} {reference : Relation Name (Node Name)}
    (bound : Binding reference) {read : Name → Wire.ReadResult (Shallow Name)}
    (sound : ReadSound read reference) {root : Name} {entries : List (Key × Name)}
    (tree : Realizes layerOf reference none root entries)
    {node : Node Name} (present : reference root node) {fuel : Nat} (enough : (node.rootContext layerOf).layer < fuel)
    {key : Key} (covers : PathCovers layerOf read key root reference) :
    route layerOf read key fuel none root = .ok (entries.lookup key) :=
  Proofs.Formats.Dasl.MstRouteComplete.route_available covers tree .start (by simp)
    (fun _ known => bound present known ▸ enough) |>.elim fun _ found => route_sound bound sound tree found ▸ found

/-- Finite validated realizations cannot hide an empty subtree behind a named
non-root child. Empty intermediate nodes must eventually reach a record. -/
theorem Realizes.nonroot_nonempty {layerOf : Key → Nat} {reference : Relation Name (Node Name)}
    {ctx : Context} {name : Name} {entries : List (Key × Name)}
    (tree : Realizes layerOf reference (some ctx) name entries) (notRoot : ctx.root = false) : entries ≠ [] :=
  Proofs.Formats.Dasl.MstRooted.nonroot_nonempty tree ⟨ctx, rfl, notRoot⟩

/-- The stored root layer is the maximum record layer of the finite represented
map, with zero as the empty-map convention. -/
theorem Realizes.rootLayer_spec {layerOf : Key → Nat} {reference : Relation Name (Node Name)} (bound : Binding reference)
    {name : Name} {entries : List (Key × Name)} (tree : Realizes layerOf reference none name entries)
    {node : Node Name} (known : reference name node) :
    (∀ pair ∈ entries, layerOf pair.1 ≤ (node.rootContext layerOf).layer) ∧
      ((node.rootContext layerOf).layer = 0 ∨ ∃ pair ∈ entries, layerOf pair.1 = (node.rootContext layerOf).layer) :=
  Proofs.Formats.Dasl.MstRooted.root_max bound tree known

end Silmaril.Formats.Dasl.Mst
