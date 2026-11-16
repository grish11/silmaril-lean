module

public import Silmaril.Libc.Contract.Inst.Defs
public import Silmaril.Project.Registry.Institution.Defs

/-!
# Logic graph: the institutions and rooms of `Silmaril.Libc`

Registrations of the institution and room declarations of the `Libc` tree (`docs/projects/logic-graph.md`): Lean checks each declaration's type; a family is registered as a family.
-/

silmaril room libc.contracts.room := Silmaril.Libc.Contracts.room
