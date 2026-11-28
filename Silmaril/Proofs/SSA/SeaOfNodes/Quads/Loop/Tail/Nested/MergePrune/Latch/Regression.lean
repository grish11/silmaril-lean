module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Comparison.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Example.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Numbered.Thms

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch

open Diamond.MLIR.CF.Example (decrement)
open Example (columns gammaArity mask overwriteAdmission refusesUsed runCF runRVSDG runSource tailPackets)

example : mask.rename decrement = none := rfl
example : gammaArity = 5 := rfl
example : overwriteAdmission = (true, true) := rfl
example : refusesUsed = (true, true, true, true) := rfl

example : columns = [(3, 41, some 7), (2, 42, some 6), (4, 43, some 10)] := by
  unfold columns Example.probe
  simp only [MergePrune.Numbered.merge_run]
  rfl

example : tailPackets = [(true, 7, 255), (true, 8, 255), (false, 16, 255)] := rfl

example : runRVSDG 3 = some 16 := by
  unfold runRVSDG
  rw [Numbered.lower_run]
  rfl
example : runRVSDG 2 = none := by
  unfold runRVSDG
  rw [Numbered.lower_run]
  rfl

example : (runSource 14, runCF 15) = (some 16, some 16) := rfl
example : (runSource 13, runCF 14) = (none, none) := rfl

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch
