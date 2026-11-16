module

public import Silmaril.Cerberus.Institution.Defs
public import Silmaril.Project.Registry.Institution.Defs

/-!
# Logic graph: the institutions and rooms of `Silmaril.Cerberus`

Registrations of the institution and room declarations of the `Cerberus` tree (`docs/projects/logic-graph.md`): Lean checks each declaration's type; a family is registered as a family.
-/

silmaril institution cerberus.institution.bundled := Silmaril.Cerberus.Institution.bundled
silmaril room cerberus.institution.room := Silmaril.Cerberus.Institution.room
