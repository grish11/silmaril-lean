module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.InstructionMap.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Version.InstructionMap.Thms
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Phi.InstructionMap

public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi

universe v w
variable {V K : Type w} {F G : Type v} [DecidableEq K]

theorem Graph.check_mapOp (f : F → G) (graph : Graph V K F) [DecidableEq V] :
    (graph.mapOp f).check = graph.check :=
  Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Phi.check_map f graph

/-- Transposing predecessor rows commutes with primitive relabelling. -/
theorem lower_mapOp (f : F → G) (graph : Graph V K F) :
    lower (graph.mapOp f) = (lower graph).mapOp f :=
  Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Phi.lower_map f graph

theorem GlobalSSA.WellFormed.mapOp (f : F → G) {graph : Graph V K F} [DecidableEq V]
    {inputs : List V} (wf : GlobalSSA.WellFormed graph inputs) :
    GlobalSSA.WellFormed (graph.mapOp f) inputs :=
  Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Phi.wellFormed_map f graph inputs wf

/-- The same arrival rows give the same checker result after opcode relabelling. -/
theorem GlobalSSA.check_mapOp (f : F → G) (graph : Graph V K F) [DecidableEq V] (inputs : List V)
    (certificate : GlobalSSA.Certificate V K) :
    GlobalSSA.check (graph.mapOp f) inputs certificate = GlobalSSA.check graph inputs certificate :=
  Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Phi.checkArrivals_map f graph inputs certificate

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi
