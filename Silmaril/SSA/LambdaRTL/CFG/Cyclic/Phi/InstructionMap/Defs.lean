module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.WellFormed.Defs

/-! # Primitive relabelling for normalized predecessor-indexed graphs -/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi

universe v w
variable {V K : Type w} {F G : Type v}

/-- Primitive relabelling only acts in the ordinary bodies. Edge operands
are values and the predecessor keys and destinations are retained verbatim. -/
def Block.mapOp (f : F → G) (block : Block V K F) : Block V K G :=
  ⟨block.rows, block.body.mapOp f⟩

def Graph.mapOp (f : F → G) (graph : Graph V K F) : Graph V K G :=
  ⟨graph.entry.mapOp f, graph.blocks.map fun (key, block) => (key, block.mapOp f)⟩

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi
