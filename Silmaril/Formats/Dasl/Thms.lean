module

public import Silmaril.Formats.Dasl.Defs
import Silmaril.Proofs.Formats.Dasl.Basic

public section

namespace Silmaril.Formats.Dasl

variable {Name Next Last : Type}

@[simp] theorem Shallow.map_id (tree : Shallow Name) : Shallow.map id tree = tree :=
  Proofs.Formats.Dasl.shallow_map_id tree

theorem Shallow.map_comp (first : Name → Next) (second : Next → Last) (tree : Shallow Name) :
    Shallow.map second (Shallow.map first tree) = Shallow.map (second ∘ first) tree :=
  Proofs.Formats.Dasl.shallow_map_comp first second tree

@[simp] theorem Shallow.shallow_embed (tree : Shallow Name) : Partial.shallow tree.embed = tree :=
  Proofs.Formats.Dasl.shallow_embed tree

theorem Extends.refl (tree : Partial Name) : Extends tree tree := .same tree

theorem Extends.trans {low mid high : Partial Name} (first : Extends low mid)
    (second : Extends mid high) : Extends low high := Proofs.Formats.Dasl.extends_trans first second

theorem Extends.antisymm {low high : Partial Name} (first : Extends low high)
    (second : Extends high low) : low = high := Proofs.Formats.Dasl.extends_antisymm first second

instance : PartialOrder (Partial Name) where
  le := Extends
  le_refl := Extends.refl
  le_trans _ _ _ := Extends.trans
  le_antisymm _ _ := Extends.antisymm

theorem Extends.shallow_eq {low high : Partial Name} (step : Extends low high) :
    low.shallow = high.shallow := Proofs.Formats.Dasl.extends_shallow_eq step

theorem Partial.shallow_le (tree : Partial Name) : tree.shallow.embed ≤ tree :=
  Proofs.Formats.Dasl.shallow_le tree

theorem Extends.bindings_subset {low high : Partial Name} (step : Extends low high) :
    low.bindings.Subset high.bindings := Proofs.Formats.Dasl.bindings_subset step

end Silmaril.Formats.Dasl
