module

public import Silmaril.LogicGraph.Nodes.Defs
public import Silmaril.Wasi.Spec.Defs
public import Silmaril.Wasi.Spec.Thms

/-!
# Logic graph: the comorphisms, morphisms and corridors of `Silmaril.Wasi`

Lean finds the endpoints of each edge among the registered institutions and rooms (`Silmaril.LogicGraph.Nodes.Defs`) and checks every listed fact.
-/

silmaril comorphism wasi.spec.inc_inst.to_wasi := Silmaril.Wasi.Spec.IncInst.toWasi (facts := [Silmaril.Wasi.Spec.IncInst.toWasi_modelExpansive])
silmaril comorphism wasi.spec.wasi_to_g_inst := Silmaril.Wasi.Spec.wasiToGInst (facts := [Silmaril.Wasi.Spec.wasiToGInst_modelExpansive])
