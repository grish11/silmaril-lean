module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Petri.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Fixture
meta import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Petri.Defs
meta import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Fixture

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Petri

open Fixture
open RVSDG (Tuple)
open RVSDG.NestedTheta.Petri (Finishes)
open RVSDG.OrderedRuntime.Structured (Threaded)

-- Sequential copies would collapse the lanes. The two exact packets
-- show the pair swapped simultaneously at each feedback.
example : Finishes (thetaRuntime 4) (lowerActivation graph) (encodeHeader ⟨0, 1, initial⟩ (input 1))
    (.cons ⟨1⟩ (encodeHeader ⟨1, 0, afterFirst⟩ (input 1))) :=
  (lowerActivation_finishes_iff graph (input 1) ⟨0, 1, initial⟩ _).mpr rfl

example : (lowerActivation graph).run (thetaRuntime 4) 0 (encodeHeader ⟨1, 0, afterFirst⟩ (input 1)) =
    some (.cons ⟨1⟩ (encodeHeader ⟨0, 1, afterSecond⟩ (input 1))) := by
  rw [lowerActivation_run]
  rfl

-- Each whole-net witness starts at a single entry marking with its own
-- input and observes all cells. Coincident inputs still execute the body.
example : Finishes (thetaRuntime 4) (lower graph) (encodeInput initial (input 1))
    (encodeResult 0 final) :=
  (lower_finishes_iff graph (input 1) initial 0 final).mpr ⟨2, rfl⟩

example : Finishes (thetaRuntime 4) (lower graph) (encodeInput initial (input 0))
    (encodeResult 0 aliased) :=
  (lower_finishes_iff graph (input 0) initial 0 aliased).mpr ⟨1, rfl⟩

private def summarize (result : Option (Tuple (WireVal 4) (Threaded wordPorts))) :
    Option (Word × Word × Word × Word × Word) :=
  result.map fun
    | .cons word (.cons heap .nil) => (word, heap 0, heap 1, heap 2, heap 3)

-- The numbered graph needs three activations for two backedges.
#guard ((lower graph).run (thetaRuntime 4) 2 (encodeInput initial (input 1))).isNone
#guard summarize ((lower graph).run (thetaRuntime 4) 3 (encodeInput initial (input 1))) ==
  some (0, 0, 0, 0, 42)
#guard ((lower graph).run (thetaRuntime 4) 1 (encodeInput initial (input 0))).isNone
#guard summarize ((lower graph).run (thetaRuntime 4) 2 (encodeInput initial (input 0))) ==
  some (0, 0, 5, 0, 42)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Petri
