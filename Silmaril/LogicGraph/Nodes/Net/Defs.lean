module

public import Silmaril.Net.Http1.Institution.Thms
public import Silmaril.Net.Udp.Institution.Thms
public import Silmaril.Project.Registry.Institution.Defs

/-!
# Logic graph: the institutions and rooms of `Silmaril.Net`

Registrations of the institution and room declarations of the `Net` tree (`docs/projects/logic-graph.md`): Lean checks each declaration's type; a family is registered as a family.
-/

silmaril room net.http1.inst.room := Silmaril.Net.Http1.Inst.room
silmaril room net.udp.inst.room := Silmaril.Net.Udp.Inst.room
