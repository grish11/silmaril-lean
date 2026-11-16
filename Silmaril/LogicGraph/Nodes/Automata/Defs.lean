module

public import Silmaril.Automata.Institution.Thms
public import Silmaril.Project.Registry.Institution.Defs

/-!
# Logic graph: the institutions and rooms of `Silmaril.Automata`

Registrations of the institution and room declarations of the `Automata` tree (`docs/projects/logic-graph.md`): Lean checks each declaration's type; a family is registered as a family.
-/

silmaril room automata.inst.room := Silmaril.Automata.Inst.room
