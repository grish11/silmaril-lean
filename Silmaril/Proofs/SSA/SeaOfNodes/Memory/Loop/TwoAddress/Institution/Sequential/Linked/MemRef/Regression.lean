module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.MemRef.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Fixture
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Fixture
meta import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.MemRef.Defs
meta import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Fixture
meta import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Fixture

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.MemRef

open Linked.Fixture (first wiring inputs)
open Sequential.Fixture (graph initial)

private def run (fuel : Nat) : Option (Word × Word × List Word) :=
  (runFuel first graph wiring inputs fuel ⟨initial⟩).map fun (firstWord, secondWord, buffer) =>
    (firstWord, secondWord, (List.finRange 6).map buffer.cell)

-- The first exit enters the second loop with the original post-store
-- buffer; each loop takes one backedge, and both frame cells survive.
#guard (run 7).isNone
#guard run 8 == some (3, 3, [11, 73, 11, 22, 91, 22])

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.MemRef
