module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission.Chain.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission.Chain.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission.Chain.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission.CaptureChain

open Example (compatible conflict aliasing successful summarize stoppedRow lastSelection)

#guard summarize compatible ==
  some ⟨true, some (1, .checker .neitherMarked), .error (.checker .neitherMarked)⟩
#guard summarize conflict ==
  some ⟨true, some (1, .checker .neitherMarked), .error .incompatibleFacts⟩
#guard summarize aliasing ==
  some ⟨false, some (1, .checker .neitherMarked), .error .aliasedWrite⟩
#guard stoppedRow == some (true, .constant ⟨false⟩, [true, false, false, true], 9, 0)
#guard summarize successful == some ⟨true, none, .ok true⟩
#guard lastSelection == some true

example : compatible.length = 3 := rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
example : summarize conflict =
    some ⟨true, some (1, .checker .neitherMarked), .error .incompatibleFacts⟩ := rfl

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission.CaptureChain
