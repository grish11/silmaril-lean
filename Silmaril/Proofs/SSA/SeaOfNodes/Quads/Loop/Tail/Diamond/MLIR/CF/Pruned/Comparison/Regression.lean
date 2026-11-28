module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Comparison.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Example.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Prune.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Categorical.Thms

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Comparison

open CF.Example (checked input source width)
open Pruned.Example (accepted mask runCF runRVSDG)
open SeaOfNodes.Loop.MLIR.CF (evalOp model)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Silmaril.MLIR.CF.SwitchAssert (Cfg)

example : (accepted.trace model 3 (mask.project ((source 4).body.eval model input))).map
    checked.predecessor = [6, 0, 6] := by
  rw [accepted.trace_agrees]
  rfl

private theorem graphRun :
    accepted.lower.run (Join.model model) 3 input = some (.cons (22 : Word width) .nil) :=
  accepted.lower_run model 3 input

example :
    (Cfg.embed (lower accepted)).denotePart evalOp (encodeValues input) =
      Part.some (.returned (.cons (22 : Word width) .nil)) := by
  rw [denotePart_eq, (accepted.lower.denotePart_eq_some (Join.model model) input _).mpr ⟨3, graphRun⟩]
  rfl

example : runRVSDG 2 = none := by
  unfold runRVSDG
  rw [accepted.lower_run]
  rfl

example : runCF 15 = none := rfl

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Comparison
