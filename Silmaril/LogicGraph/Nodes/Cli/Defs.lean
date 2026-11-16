module

public import Silmaril.Cli.Institution.Defs
public import Silmaril.Project.Registry.Institution.Defs

/-!
# Logic graph: the institutions and rooms of `Silmaril.Cli`

Registrations of the institution and room declarations of the `Cli` tree (`docs/projects/logic-graph.md`): Lean checks each declaration's type; a family is registered as a family.
-/

silmaril room cli.institution.room := Silmaril.Cli.Institution.room
