module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Petri.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.MemRef.Regression
meta import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Petri.Defs
meta import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.MemRef.Regression

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Petri

open Fixture
open RVSDG (Tuple)
open RVSDG.NestedTheta.Petri (Finishes)
open RVSDG.OrderedRuntime.Structured (Threaded)

-- The emitted θ body produces both the restart tag and the next arrival
-- colour. That carried tuple is the input to the second activation.
example : (lowerBody graph).run (thetaRuntime 3) 0 (encodeArrival .entry (initial 7) (input 1)) =
    some (.cons ⟨1⟩ (encodeArrival .backedge afterEntry (input 1))) := by
  rw [lowerBody_run]
  rfl

example : (lowerBody graph).run (thetaRuntime 3) 0 (encodeArrival .backedge afterEntry (input 1)) =
    some (.cons ⟨0⟩ (encodeArrival .entry afterFeedback (input 1))) := by
  rw [lowerBody_run]
  rfl

-- One completed firing trace starts from the emitted net's initial
-- marking and reaches the result with both updated cells and the sentinel.
example : Finishes (thetaRuntime 3) (lower graph) (encodeArrival .entry (initial 7) (input 1))
    (encodeResult 0 afterFeedback) :=
  (lower_finishes_iff graph (input 1) (initial 7) 0 afterFeedback).mpr ⟨1, rfl⟩

-- Immediate exit is also a completed trace and still performs the store.
example : Finishes (thetaRuntime 3) (lower graph) (encodeArrival .entry (initial 0) (input 1))
    (encodeResult 0 ((initial 0).write 0 9)) :=
  (lower_finishes_iff graph (input 1) (initial 0) 0 ((initial 0).write 0 9)).mpr ⟨0, rfl⟩

private def summarize (result : Option (Tuple (WireVal 3) (Threaded wordPorts))) :
    Option (Word × Word × Word × Word) :=
  result.map fun
    | .cons word (.cons heap .nil) => (word, heap 0, heap 1, heap 2)

#guard ((lower graph).run (thetaRuntime 3) 1 (encodeArrival .entry (initial 7) (input 1))).isNone
#guard summarize ((lower graph).run (thetaRuntime 3) 2 (encodeArrival .entry (initial 7) (input 1))) ==
  some (0, 9, 9, 99)
#guard summarize ((lower graph).run (thetaRuntime 3) 1 (encodeArrival .entry (initial 0) (input 1))) ==
  some (0, 9, 0, 99)

-- With coincident ports the first store overwrites the only chosen cell.
#guard ((lower graph).run (thetaRuntime 3) 5 (encodeArrival .entry (initial 7) (input 0))).isNone

end Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Petri
