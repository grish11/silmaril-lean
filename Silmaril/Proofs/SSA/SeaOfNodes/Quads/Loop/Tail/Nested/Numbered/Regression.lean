module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Numbered.Comparison.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Numbered.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Numbered

open Nested.MLIR.CF.Example (mask incomingResults runCF runSource)
open Diamond.MLIR.CF.Example (test)
open Example (incoming runRVSDG sourceBudget thetaArity)

example : incomingResults = [7, 6, 10] := rfl
example : incoming = [(3, some 7), (2, some 6), (4, some 10)] := by
  unfold incoming Example.probe
  simp only [merge_run]
  rfl
example : thetaArity = 6 := rfl
example : mask.rename test = none := rfl

example : sourceBudget 3 = 14 := rfl
example : sourceBudget 2 = 10 := rfl
example : runRVSDG 3 = some 16 := by
  unfold runRVSDG
  rw [lower_run]
  rfl
example : runRVSDG 2 = none := by
  unfold runRVSDG
  rw [lower_run]
  rfl
example : (runSource 14, runCF 15) = (some 16, some 16) := rfl
example : (runSource 13, runCF 14) = (none, none) := rfl

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Numbered
