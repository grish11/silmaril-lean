module

public import Silmaril.Containers.Image.Defs

/-!
# Proofs: container images

Proofs for `Silmaril.Containers.Image.Thms`. Nothing imports this module except that header.
-/

public section

namespace Silmaril.Proofs.Containers.Image

open Silmaril.Containers Silmaril.Containers.Cas

theorem flatten_config {D C : Type} {S : Stores D C} {m : Layered D} {img : Flat C}
    (h : m.flatten S = some img) : S.configs m.config = some img.config := by
  unfold Layered.flatten at h
  cases hc : S.configs m.config <;> cases hl : m.layers.mapM S.layers <;>
    simp_all [bind, Option.bind, pure] <;> (subst h; rfl)

/-- `mapM` into `Option` fails when it fails on one element. -/
theorem mapM_option_eq_none {α β : Type} {f : α → Option β} {a : α} :
    ∀ {l : List α}, a ∈ l → f a = none → l.mapM f = none
  | _ :: l, .head _, h => by simp [List.mapM_cons, h, bind, Option.bind]
  | b :: l, .tail _ hm, h => by
    simp only [List.mapM_cons, mapM_option_eq_none hm h]
    cases f b <;> rfl

theorem flatten_none_of_layer {D C : Type} {S : Stores D C} {m : Layered D} {d : D}
    (hd : d ∈ m.layers) (hS : S.layers d = none) : m.flatten S = none := by
  have : m.layers.mapM S.layers = none := mapM_option_eq_none hd hS
  unfold Layered.flatten
  cases S.configs m.config <;> simp [this, bind, Option.bind]

end Silmaril.Proofs.Containers.Image
