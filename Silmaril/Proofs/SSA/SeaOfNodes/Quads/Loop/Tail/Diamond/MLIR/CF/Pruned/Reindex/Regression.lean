module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex.Example.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Prune.Thms

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex

open CF.Example (width)
open Pruned.Example (accepted)
open Reindex.Example (order original paired wrongPairing predicateBit predecessors results)
open SeaOfNodes.Loop.MLIR.CF (model)

example : pull order paired = original := rfl
example : predicateBit = 1 := rfl
example : predecessors = [6, 0, 6] := rfl

example : results paired 3 16 = (some 22, some 22) := by
  unfold results
  rw [graph_run, cf_run, accepted.lower_run, Pruned.lower_run]
  rfl

example : results wrongPairing 3 16 = (some 34, some 34) := by
  unfold results
  rw [graph_run, cf_run, accepted.lower_run, Pruned.lower_run]
  rfl

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex
