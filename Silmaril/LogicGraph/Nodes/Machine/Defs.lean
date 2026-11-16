module

public import Silmaril.Machine.Abi.Defs
public import Silmaril.Project.Registry.Institution.Defs

/-!
# Logic graph: the institutions and rooms of `Silmaril.Machine`

Registrations of the institution and room declarations of the `Machine` tree (`docs/projects/logic-graph.md`): Lean checks each declaration's type; a family is registered as a family.
-/

silmaril institution machine.abi.logic.inst := Silmaril.Machine.Abi.Logic.inst
silmaril room machine.abi.logic.room := Silmaril.Machine.Abi.Logic.room
