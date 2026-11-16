module

public import Silmaril.Courses.Cambridge.OptimisingCompilers.Institutions.Observational
public import Silmaril.Courses.Cambridge.OptimisingCompilers.Institutions.Signature
public import Silmaril.LogicGraph.Nodes.Defs

/-!
# Logic graph: the comorphisms, morphisms and corridors of `Silmaril.Courses`

Lean finds the endpoints of each edge among the registered institutions and rooms (`Silmaril.LogicGraph.Nodes.Defs`) and checks every listed fact.
-/

silmaril comorphism courses.cambridge.optimising_compilers.institutions.sound_family.co_hom := Silmaril.Courses.Cambridge.OptimisingCompilers.Institutions.SoundFamily.coHom
silmaril comorphism courses.cambridge.optimising_compilers.institutions.state_logic.comorphism.co_hom := Silmaril.Courses.Cambridge.OptimisingCompilers.Institutions.StateLogic.Comorphism.coHom
