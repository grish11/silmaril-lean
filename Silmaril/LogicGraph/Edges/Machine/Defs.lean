module

public import Silmaril.LogicGraph.Nodes.Defs
public import Silmaril.Machine.Abi.Defs
public import Silmaril.Machine.Abi.SystemV.Thms
public import Silmaril.Machine.Abi.Win64.Thms

/-!
# Logic graph: the comorphisms, morphisms and corridors of `Silmaril.Machine`

Lean finds the endpoints of each edge among the registered institutions and rooms (`Silmaril.LogicGraph.Nodes.Defs`) and checks every listed fact.
-/

silmaril comorphism machine.abi.convention.co_hom := Silmaril.Machine.Abi.Convention.coHom
silmaril comorphism machine.abi.system_v.sysv_co_hom := Silmaril.Machine.Abi.SystemV.sysvCoHom
silmaril comorphism machine.abi.translation.co_hom := Silmaril.Machine.Abi.Translation.coHom
silmaril comorphism machine.abi.win64.win64_co_hom := Silmaril.Machine.Abi.Win64.win64CoHom
