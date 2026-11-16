module

public import Silmaril.Project.Registry.Institution.Defs
public import Silmaril.Servers.Core.Defs
public import Silmaril.Servers.OpenApi.Thms

/-!
# Logic graph: the institutions and rooms of `Silmaril.Servers`

Registrations of the institution and room declarations of the `Servers` tree (`docs/projects/logic-graph.md`): Lean checks each declaration's type; a family is registered as a family.
-/

silmaril room servers.open_api_inst.room := Silmaril.Servers.OpenApiInst.room
silmaril room servers.room := Silmaril.Servers.room
