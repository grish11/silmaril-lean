module

public import Silmaril.Courses.Cambridge.OptimisingCompilers.Institutions.Observational
public import Silmaril.Courses.Cambridge.OptimisingCompilers.Institutions.Relational
public import Silmaril.Courses.Cambridge.OptimisingCompilers.Institutions.Signature
public import Silmaril.Courses.Cambridge.OptimisingCompilers.Institutions.Transitions
public import Silmaril.Project.Registry.Institution.Defs

/-!
# Logic graph: the institutions and rooms of `Silmaril.Courses`

Registrations of the institution and room declarations of the `Courses` tree (`docs/projects/logic-graph.md`): Lean checks each declaration's type; a family is registered as a family.
-/

silmaril institution courses.cambridge.optimising_compilers.institutions.state_logic.inst := Silmaril.Courses.Cambridge.OptimisingCompilers.Institutions.StateLogic.inst
silmaril room courses.cambridge.optimising_compilers.institutions.state_logic.room := Silmaril.Courses.Cambridge.OptimisingCompilers.Institutions.StateLogic.room
silmaril room courses.cambridge.optimising_compilers.institutions.obs_room := Silmaril.Courses.Cambridge.OptimisingCompilers.Institutions.obsRoom
silmaril room courses.cambridge.optimising_compilers.institutions.rel_room := Silmaril.Courses.Cambridge.OptimisingCompilers.Institutions.relRoom
silmaril room courses.cambridge.optimising_compilers.institutions.trans_room := Silmaril.Courses.Cambridge.OptimisingCompilers.Institutions.transRoom
