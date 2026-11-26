module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Fixture
meta import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Fixture
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Fixture
meta import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Defs
meta import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Fixture

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked

open RVSDG (Tuple)
open Sequential.Fixture (graph initial left right model next)
open Sequential.Linked.Fixture (first wiring inputs)

example (word : Word) : wiring.select word inputs = CellEmbedding.input right (next word) := rfl

private def run (fuel : Nat) : Option (Word × Word × List Word) :=
  ((lower first graph wiring).run (thetaRuntime 6) fuel (encodeInput initial inputs)).map fun raw =>
    let (word, nextWord, heap) := (resultCodec 6).symm raw
    (word, nextWord, (List.finRange 6).map heap)

-- Two actual θ vertices share a live heap in one compiled graph. Each
-- requires its initial activation and one backedge on these inputs.
#guard (run 1).isNone
#guard run 2 == some (3, 3, [11, 73, 11, 22, 91, 22])

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked
