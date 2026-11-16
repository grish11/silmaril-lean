module

public import Silmaril.Calculi.LambdaCube.PER.PTSMorphism
public import Silmaril.Calculi.LambdaCube.STLC.Defs
public import Silmaril.Calculi.LambdaCube.Semantics
public import Silmaril.Project.Registry.Institution.Defs

/-!
# Logic graph: the institutions and rooms of `Silmaril.Calculi`

Registrations of the institution and room declarations of the `Calculi` tree (`docs/projects/logic-graph.md`): Lean checks each declaration's type; a family is registered as a family.
-/

silmaril institution calculi.lambda_cube.g_semantics.inst := Silmaril.Calculi.LambdaCube.GSemantics.inst
silmaril institution calculi.lambda_cube.semantics.inst := Silmaril.Calculi.LambdaCube.Semantics.inst
silmaril room calculi.lambda_cube.g_semantics.room := Silmaril.Calculi.LambdaCube.GSemantics.room
silmaril room calculi.lambda_cube.stlc.room := Silmaril.Calculi.LambdaCube.STLC.room
silmaril room calculi.lambda_cube.semantics.room := Silmaril.Calculi.LambdaCube.Semantics.room
