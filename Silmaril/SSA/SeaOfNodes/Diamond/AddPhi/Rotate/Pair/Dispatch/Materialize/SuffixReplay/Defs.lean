module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Defs
public import Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay.Defs

/-! Replay checked word rewrites on an actual emitted diamond suffix. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.SuffixReplay

open Pure.SubZero (word)

variable {inputs joined : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}

def blockOf (p : Program inputs sigs joined) : Pure.SuffixReplay.Block (word :: joined) [] :=
  ⟨p.suffix.sigs, p.suffix.dataflow, .cons p.suffix.result .nil⟩

abbrev Request (p : Program inputs sigs joined) :=
  Pure.SuffixReplay.Request (word :: joined) p.suffix.sigs

/-- The pure driver sees the actual continuation and its complete return
packet. Only an entirely accepted request list produces a graph. -/
def rewrite (p : Program inputs sigs joined) (requests : List (Request p)) :
    Except Pure.SuffixReplay.Failure (Program inputs sigs joined) :=
  (Pure.SuffixReplay.run (blockOf p) requests).map fun state => { p with suffix := state.block.program }

end Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.SuffixReplay
