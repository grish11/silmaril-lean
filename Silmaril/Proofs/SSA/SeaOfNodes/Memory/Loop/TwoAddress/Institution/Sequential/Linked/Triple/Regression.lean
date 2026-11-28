module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Fixture
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Thms
meta import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Defs
meta import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Fixture

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple

open Sequential.Fixture (captures graph initial)
open Linked.Fixture (combined first wiring inputs)
open Triple.Fixture (thirdWiring entryModel afterFirst afterSecond expected thirdInput)

private def run (fuel : Nat) : Option (Word × Word × Word × List Word) :=
  ((program first graph graph wiring thirdWiring).graph.run (thetaRuntime 6) fuel (encodeInput initial inputs)).map
    fun raw =>
      let (firstWord, secondWord, thirdWord, heap) := (resultCodec 6).symm raw
      (firstWord, secondWord, thirdWord, (List.finRange 6).map heap)

#guard (run 1).isNone
#guard run 2 == some (3, 3, 22, [11, 73, 11, 3, 91, 22])

-- The same typed captures and budget cannot return from the stale heap.
#guard ((Petri.lower graph).run (thetaRuntime 6) 2 (encodeInput initial thirdInput)).isNone

private theorem staged :
    ∃ firstHeap secondHeap,
      (Petri.lower first).Returns (thetaRuntime 6) (encodeInput initial inputs) (encodeResult 3 firstHeap) ∧
      (Petri.lower graph).Returns (thetaRuntime 6) (encodeInput firstHeap (wiring.select 3 inputs))
        (encodeResult 3 secondHeap) ∧
      (Petri.lower graph).Returns (thetaRuntime 6) (encodeInput secondHeap thirdInput)
        (encodeResult 22 expected.2.2.2) := by
  exact ⟨afterFirst, afterSecond, ⟨2, rfl⟩, ⟨2, rfl⟩, ⟨1, rfl⟩⟩

example : RVSDG.NestedTheta.Petri.Finishes (thetaRuntime 6) (lower first graph graph wiring thirdWiring)
    (encodeInput initial inputs) (resultCodec 6 expected) := by
  apply (RVSDG.NestedTheta.Petri.finishes_iff _ _ _ _).mpr
  exact (returns_iff_stages (P := combined) (Q := captures) (R := captures) first graph graph
    wiring thirdWiring entryModel initial _ 3 3 22).mpr staged

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple
