module

public import Silmaril.Project.Registry.Institution.Defs
public import Silmaril.SSA.LambdaRTL.Institution.Defs
public import Silmaril.SSA.LambdaRTL.Loop.Institution.Defs
public import Silmaril.SSA.LambdaRTL.Nameless.Institution.Defs
public import Silmaril.SSA.LambdaRTL.Version.Institution.Defs

/-!
# Logic graph: the institutions and rooms of `Silmaril.SSA`

Registrations of the institution and room declarations of the `SSA` tree (`docs/projects/logic-graph.md`): Lean checks each declaration's type; a family is registered as a family.
-/

silmaril institution ssa.lambda_rtl.institution.db_inst := Silmaril.SSA.LambdaRTL.Institution.dbInst
silmaril institution ssa.lambda_rtl.institution.logic_inst := Silmaril.SSA.LambdaRTL.Institution.logicInst
silmaril institution ssa.lambda_rtl.institution.rtl_full := Silmaril.SSA.LambdaRTL.Institution.rtlFull
silmaril institution ssa.lambda_rtl.institution.rtl_obs := Silmaril.SSA.LambdaRTL.Institution.rtlObs
silmaril institution ssa.lambda_rtl.institution.rtl_obs_l := Silmaril.SSA.LambdaRTL.Institution.rtlObsL
silmaril institution ssa.lambda_rtl.institution.ssa := Silmaril.SSA.LambdaRTL.Institution.ssa
silmaril institution ssa.lambda_rtl.institution.ssa_l := Silmaril.SSA.LambdaRTL.Institution.ssaL
silmaril institution ssa.lambda_rtl.loop.institution.loop_rtl_obs := Silmaril.SSA.LambdaRTL.Loop.Institution.loopRTLObs
silmaril institution ssa.lambda_rtl.loop.institution.loop_ssa := Silmaril.SSA.LambdaRTL.Loop.Institution.loopSSA
silmaril room ssa.lambda_rtl.institution.db_room := Silmaril.SSA.LambdaRTL.Institution.dbRoom
silmaril room ssa.lambda_rtl.institution.rtl_full_room := Silmaril.SSA.LambdaRTL.Institution.rtlFullRoom
silmaril room ssa.lambda_rtl.institution.rtl_obs_l_room := Silmaril.SSA.LambdaRTL.Institution.rtlObsLRoom
silmaril room ssa.lambda_rtl.institution.rtl_obs_room := Silmaril.SSA.LambdaRTL.Institution.rtlObsRoom
silmaril room ssa.lambda_rtl.institution.ssa_l_room := Silmaril.SSA.LambdaRTL.Institution.ssaLRoom
silmaril room ssa.lambda_rtl.institution.ssa_room := Silmaril.SSA.LambdaRTL.Institution.ssaRoom
silmaril room ssa.lambda_rtl.loop.institution.rtl_obs_room := Silmaril.SSA.LambdaRTL.Loop.Institution.rtlObsRoom
silmaril room ssa.lambda_rtl.loop.institution.ssa_room := Silmaril.SSA.LambdaRTL.Loop.Institution.ssaRoom
