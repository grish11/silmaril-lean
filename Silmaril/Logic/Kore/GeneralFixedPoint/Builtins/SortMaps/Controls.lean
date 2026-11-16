module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Defs

@[expose] public section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Controls
open CategoryTheory

abbrev source : Signature where
  bindings := ⟨"Int", "Bool", by decide⟩
  scope := ⟨[], [], []⟩
  literalPrefix := "source"
  literals := []
  hooks := []

abbrev target : Signature where
  bindings := ⟨"Integer", "Boolean", by decide⟩
  scope := ⟨[], [], []⟩
  literalPrefix := "target"
  literals := []
  hooks := []

/-- The signature has no ordinary operations; its actual String-indexed models
still have every carrier, including the designated builtin carriers. -/
def aliasMap : source ⟶ target where
  native :=
    { sorts := fun s => if s = "Int" then "Integer" else "Boolean"
      operations := by
        intro n inputs output op
        have missing : op.val ∈ ([] : List Kore.Modules.NamedSymbol) := op.property.1
        simp at missing }
  integer := by decide
  boolean := by decide
  labels := by
    intro n inputs output op
    have missing : op.val ∈ ([] : List Kore.Modules.NamedSymbol) := op.property.1
    simp at missing

/-- Ordinary sorts may alias each other and the Bool carrier. -/
example : aliasMap.native.sorts "CfgA" = aliasMap.native.sorts "CfgB" := by decide
example : aliasMap.native.sorts "CfgA" = target.bindings.boolSort := by decide

/-- A map collapsing the designated Int and Bool names is inadmissible. -/
example : ¬ ∃ f : source ⟶ target,
    f.native.sorts source.bindings.intSort = f.native.sorts source.bindings.boolSort := by
  rintro ⟨f, collapsed⟩
  exact f.builtin_images_distinct collapsed

end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Controls
