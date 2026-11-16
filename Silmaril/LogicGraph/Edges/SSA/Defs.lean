module

public import Silmaril.LogicGraph.Nodes.Defs
public import Silmaril.SSA.LambdaRTL.Institution.Defs
public import Silmaril.SSA.LambdaRTL.Loop.Institution.Defs
public import Silmaril.SSA.LambdaRTL.Nameless.Institution.Defs
public import Silmaril.SSA.LambdaRTL.Version.Institution.Defs

/-!
# Logic graph: the comorphisms, morphisms and corridors of `Silmaril.SSA`

Lean finds the endpoints of each edge among the registered institutions and rooms (`Silmaril.LogicGraph.Nodes.Defs`) and checks every listed fact.
-/

silmaril comorphism ssa.lambda_rtl.institution.of_db_co_hom := Silmaril.SSA.LambdaRTL.Institution.ofDBCoHom
silmaril comorphism ssa.lambda_rtl.institution.ssa_to_rtl := Silmaril.SSA.LambdaRTL.Institution.ssaToRTL
silmaril comorphism ssa.lambda_rtl.institution.to_db_co_hom := Silmaril.SSA.LambdaRTL.Institution.toDBCoHom
silmaril comorphism ssa.lambda_rtl.institution.version_co_hom := Silmaril.SSA.LambdaRTL.Institution.versionCoHom
silmaril comorphism ssa.lambda_rtl.loop.institution.acyclic_to_loop_ssa := Silmaril.SSA.LambdaRTL.Loop.Institution.acyclicToLoopSSA
silmaril comorphism ssa.lambda_rtl.loop.institution.loop_ssa_to_rtl := Silmaril.SSA.LambdaRTL.Loop.Institution.loopSSAToRTL
