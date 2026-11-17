module

public import Silmaril.Project.Registry.Institution.Defs
public import Silmaril.Containers.Institution.Defs

/-!
# Logic graph: the institutions and rooms of `Silmaril.Containers`

Registrations of the institution and room declarations of the `Containers` tree
(`docs/projects/logic-graph.md`, `docs/projects/containers.md`).
-/

silmaril institution containers.behaviour := Silmaril.Containers.Inst.bundled
silmaril room containers.behaviour.room := Silmaril.Containers.Inst.room
