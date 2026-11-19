module

public import Silmaril.Containers.Image.Defs
import Silmaril.Proofs.Containers.Image.Basic

/-!
# Container images: theorems

PROVED (standard axioms). Proofs longer than a few lines are in
`Silmaril.Proofs.Containers.Image` and only pointed at from here.

* `Tree.resolve_file`: a complete tree of digests resolves each file to its blob;
* `Layered.flatten_config`: a flattened image has the configuration its manifest names;
* `mapM_option_eq_none`, `Layered.flatten_none_of_layer`: a missing layer makes flattening
  fail (the runtime refuses the image; it does not run a partial one);
* `Shape.entry_program`: the entry-point shape reads the executable file at the entry point.
-/

public section

namespace Silmaril.Containers

open Silmaril.Containers.Cas

theorem Tree.resolve_file {C D : Type} {S : Store D C} {t : Tree D} {p : Path} {d : D}
    {x : Bool} {c : C} (ht : t p = some (.file d x)) (hS : S d = some c) :
    t.resolve S p = some (.file c x) := by
  simp [Tree.resolve, ht, hS]

theorem Layered.flatten_config {D C : Type} {S : Stores D C} {m : Layered D} {img : Flat C}
    (h : m.flatten S = some img) : S.configs m.config = some img.config :=
  Silmaril.Proofs.Containers.Image.flatten_config h

theorem mapM_option_eq_none {α β : Type} {f : α → Option β} {a : α} {l : List α} (hm : a ∈ l)
    (h : f a = none) : l.mapM f = none :=
  Silmaril.Proofs.Containers.Image.mapM_option_eq_none hm h

theorem Layered.flatten_none_of_layer {D C : Type} {S : Stores D C} {m : Layered D} {d : D}
    (hd : d ∈ m.layers) (hS : S.layers d = none) : m.flatten S = none :=
  Silmaril.Proofs.Containers.Image.flatten_none_of_layer hd hS

theorem Shape.entry_program {C P : Type} {k : ShapeKind} {dec : C → Option P} {img : Flat C}
    {p : Path} {c : C} (hp : img.config.entryPath = some p)
    (hc : img.root p = some (.file c true)) :
    (Shape.entry k dec).program img = dec c := by
  simp [Shape.entry, hp, hc, bind, Option.bind]

end Silmaril.Containers
