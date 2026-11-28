module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Defs

/-! Deterministic discovery for the checked reuse of a shared entry add. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Discovery

open Pure.SubZero (word)

variable {inputs : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}

/-- Take the first word producer in shared table order accepted by the
ordered-key and two-occurrence provenance check. -/
def findRepresentative? (p : Program inputs sigs [word]) : Option (EntryAdd p) :=
  (Pure.RightIdentityPass.wordProducers p.diamond.shared).find? (check p)

/-- Discover an entry representative and use the existing checked emitter,
which also checks the actual right-materialized suffix. -/
def discoverAndRewrite? (p : Program inputs sigs [word]) : Option (Program inputs sigs [word, word]) :=
  (findRepresentative? p).bind (rewrite? p)

end Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Discovery
