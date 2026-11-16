module

public import Silmaril.Games.DInstitution.Defs
public import Silmaril.Games.InstGraph.Defs
public import Silmaril.Games.Institution.Defs
public import Silmaril.Games.Reindex.Defs
public import Silmaril.LogicGraph.Nodes.Defs
public import Silmaril.Wasi.Spec.Thms

/-!
# Logic graph: the comorphisms, morphisms and corridors of `Silmaril.Games`

Lean finds the endpoints of each edge among the registered institutions and rooms (`Silmaril.LogicGraph.Nodes.Defs`) and checks every listed fact.
-/

silmaril comorphism games.g_inst.along_co_hom := Silmaril.Games.GInst.alongCoHom (facts := [Silmaril.Games.GInst.alongCoHom_modelExpansive])
silmaril comorphism games.g_inst.reindex := Silmaril.Games.GInst.reindex
silmaril comorphism games.g_inst.to_dg_inst := Silmaril.Games.GInst.toDGInst (facts := [Silmaril.Games.GInst.toDGInst_modelExpansive])
silmaril comorphism games.g_inst_ref.to_g_inst := Silmaril.Games.GInstRef.toGInst (facts := [Silmaril.Games.GInstRef.toGInst_modelExpansive])
silmaril comorphism games.inst_graph.comor := Silmaril.Games.InstGraph.comor (facts := [Silmaril.Games.InstGraph.edge_modelExpansive])
