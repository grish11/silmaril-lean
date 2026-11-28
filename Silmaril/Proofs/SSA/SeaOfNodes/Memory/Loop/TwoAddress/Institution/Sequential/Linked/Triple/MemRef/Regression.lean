module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.MemRef.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Fixture
meta import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.MemRef.Defs
meta import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Fixture

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.MemRef

open Sequential.Fixture (captures graph initial)
open Linked.Fixture (combined first wiring inputs)
open Triple.Fixture (thirdWiring entryModel afterFirst afterSecond expected thirdInput)

private def run (fuel : Nat) : Option (Word × Word × Word × List Word) :=
  (runFuel first graph graph wiring thirdWiring inputs fuel ⟨initial⟩).map
    fun (firstWord, secondWord, thirdWord, buffer) =>
      (firstWord, secondWord, thirdWord, (List.finRange 6).map buffer.cell)

-- The pair executes eight blocks and the third loop executes three.
#guard (run 10).isNone
#guard run 11 == some (3, 3, 22, [11, 73, 11, 3, 91, 22])

-- At the same third-stage inputs and fuel, the original heap cannot
-- supply 22 to the load. The carried heap returns it immediately.
#guard (TwoAddress.MemRef.runFuel graph thirdInput 3 ⟨initial⟩).isNone
#guard ((TwoAddress.MemRef.runFuel graph thirdInput 3 ⟨afterSecond⟩).map Prod.fst) == some (22 : Word)

example : ∃ fuel,
    runFuel first graph graph wiring thirdWiring inputs fuel ⟨initial⟩ = some (3, 3, 22, ⟨expected.2.2.2⟩) := by
  apply (returns_iff_numbered (P := combined) (Q := captures) (R := captures) first graph graph
    wiring thirdWiring entryModel initial expected.2.2.2 3 3 22).mpr
  exact (Triple.returns_iff_stages first graph graph wiring thirdWiring entryModel initial expected.2.2.2 3 3 22).mpr
    ⟨afterFirst, afterSecond, ⟨2, rfl⟩, ⟨2, rfl⟩, ⟨1, rfl⟩⟩

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.MemRef
