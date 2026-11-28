module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.SuffixReplay.Defs
public import Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay.Discovery.Defs

/-! Discover shrinking edits in the actual emitted post-join suffix. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.SuffixReplay.Discovery

variable {inputs joined : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}

/-- The complete packet of this continuation is its single return wire.
The diamond and runtime capture are carried through verbatim. -/
def normalize (p : Program inputs sigs joined) : Program inputs sigs joined :=
  let final := Pure.SuffixReplay.Discovery.normalize (blockOf p)
  { p with suffix := final.state.block.program }

end Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.SuffixReplay.Discovery
