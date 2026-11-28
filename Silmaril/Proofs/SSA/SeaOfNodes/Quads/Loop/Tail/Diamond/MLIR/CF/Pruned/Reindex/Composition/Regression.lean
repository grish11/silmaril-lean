module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex.Composition.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex.Composition.Example.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Prune.Thms

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex.Composition

open Composition.Example (first second reversed paired predicateBit predecessors sequentialResults results)
open Reindex.Example (original)
open CF.Example (regs)
open Pruned.Example (accepted)
open SeaOfNodes.Diamond (dataPorts)

example : graph (Permutation.refl (dataPorts regs)) accepted.lower = accepted.lower :=
  graph_refl _
example : lowerCF (Permutation.refl (dataPorts regs)) accepted = Pruned.lower accepted :=
  lowerCF_refl _

example : pull (first.trans second) paired = original := rfl
example : predicateBit = 1 := rfl
example : predecessors = [6, 0, 6] := rfl

example : sequentialResults = results (first.trans second) := by
  unfold sequentialResults results
  rw [graph_trans, lowerCF_trans]

example : results (first.trans second) = (some 22, some 22) := by
  unfold results
  rw [graph_run, cf_run, accepted.lower_run, Pruned.lower_run]
  rfl

example : results reversed = (some 86, some 86) := by
  unfold results
  rw [graph_run, cf_run, accepted.lower_run, Pruned.lower_run]
  rfl

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex.Composition
