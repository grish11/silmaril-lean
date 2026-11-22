module

public import Silmaril.Calculi.PERConstraints.Syntax.Defs
public import Silmaril.Formats.Dasl.Thms
public import Silmaril.Formats.Json.Extensional

/-! Chosen syntax translations for DASL shallow trees and extensional JSON.
JSON replacements can insert whole trees; DASL here only renames link names. -/

@[expose] public section
namespace Silmaril.Calculi.PERConstraints

open CategoryTheory Silmaril.Formats

/-- Types of atoms, with replacement by extensional JSON over fixed object keys. -/
structure JsonAtoms (Key : Type) where
  Atom : Type

instance (Key : Type) : Category (JsonAtoms Key) where
  Hom source target := source.Atom → Json target.Atom Key
  id _ := Json.scalar
  comp first second atom := (first atom).bind second
  id_comp _ := rfl
  comp_id replacement := funext fun atom => Json.bind_pure (replacement atom)
  assoc first second third := funext fun atom => Json.bind_assoc (first atom) second third

/-- Extend replacements to total maps on JSON trees. -/
def jsonSyntax (Key : Type) : JsonAtoms Key ⥤ Syntax where
  obj atoms := ⟨Json atoms.Atom Key⟩
  map replacement := ⟨fun tree => tree.bind replacement⟩
  map_id _ := Syntax.Hom.ext (funext Json.bind_pure)
  map_comp first second := Syntax.Hom.ext (funext fun tree => (tree.bind_assoc first second).symm)

/-- Rename shallow DASL references without changing inline data. -/
def daslSyntax : Type ⥤ Syntax where
  obj names := ⟨Dasl.Shallow names⟩
  map rename := ⟨Dasl.Shallow.map rename⟩
  map_id _ := Syntax.Hom.ext (funext Dasl.Shallow.map_id)
  map_comp first second := Syntax.Hom.ext (funext fun tree => (tree.map_comp first second).symm)

end Silmaril.Calculi.PERConstraints
