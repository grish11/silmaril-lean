module

public import Silmaril.Calculi.LambdaCube.Hets.Defs
public import Silmaril.Calculi.LambdaCube.Hets.Thms
public import Silmaril.Calculi.LambdaCube.PER.CubeMorphisms.Defs
public import Silmaril.Calculi.LambdaCube.PER.PTSMorphism
public import Silmaril.Calculi.LambdaCube.Semantics
public import Silmaril.LogicGraph.Nodes.Defs

/-!
# Logic graph: the comorphisms, morphisms and corridors of `Silmaril.Calculi`

Lean finds the endpoints of each edge among the registered institutions and rooms (`Silmaril.LogicGraph.Nodes.Defs`) and checks every listed fact.
-/

silmaril comorphism calculi.lambda_cube.g_semantics.pullback_comorphism := Silmaril.Calculi.LambdaCube.GSemantics.pullbackComorphism
silmaril comorphism calculi.lambda_cube.per_model.system_f.stlc_comorphism := Silmaril.Calculi.LambdaCube.PERModel.SystemF.stlcComorphism
silmaril comorphism calculi.lambda_cube.per_model.system_f_omega.omega_comorphism := Silmaril.Calculi.LambdaCube.PERModel.SystemFOmega.omegaComorphism
silmaril comorphism calculi.lambda_cube.per_model.system_f_omega.stlc_comorphism := Silmaril.Calculi.LambdaCube.PERModel.SystemFOmega.stlcComorphism
silmaril comorphism calculi.lambda_cube.per_model.system_f_omega.system_f_comorphism := Silmaril.Calculi.LambdaCube.PERModel.SystemFOmega.systemFComorphism
silmaril comorphism calculi.lambda_cube.restriction_graph.comorphism := Silmaril.Calculi.LambdaCube.RestrictionGraph.comorphism (facts := [Silmaril.Calculi.LambdaCube.RestrictionGraph.comorphism_modelExpansive])
silmaril comorphism calculi.lambda_cube.semantic_inclusion.comorphism := Silmaril.Calculi.LambdaCube.SemanticInclusion.comorphism
silmaril comorphism calculi.lambda_cube.semantics.restrict_comorphism := Silmaril.Calculi.LambdaCube.Semantics.restrictComorphism
silmaril morphism calculi.lambda_cube.restriction_graph.projection := Silmaril.Calculi.LambdaCube.RestrictionGraph.projection
