module

public import Silmaril.Games.DInstitution.Defs
public import Silmaril.Games.InstGraph.Defs
public import Silmaril.Games.Institution.Defs
public import Silmaril.Games.Reindex.Defs
public import Silmaril.Project.Registry.Institution.Defs

/-!
# Logic graph: the institutions and rooms of `Silmaril.Games`

Registrations of the institution and room declarations of the `Games` tree (`docs/projects/logic-graph.md`): Lean checks each declaration's type; a family is registered as a family.
-/

silmaril institution games.dg_inst := Silmaril.Games.DGInst
silmaril institution games.g_inst := Silmaril.Games.GInst
silmaril institution games.g_inst.along := Silmaril.Games.GInst.along
silmaril institution games.g_inst_ref := Silmaril.Games.GInstRef
silmaril institution games.inst_graph.inst := Silmaril.Games.InstGraph.inst
silmaril room games.dg_inst.room := Silmaril.Games.DGInst.room
silmaril room games.g_inst.room := Silmaril.Games.GInst.room
silmaril room games.g_inst.room_ref := Silmaril.Games.GInst.roomRef
