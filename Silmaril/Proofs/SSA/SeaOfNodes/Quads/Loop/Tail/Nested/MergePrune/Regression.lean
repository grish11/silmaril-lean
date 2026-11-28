module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Comparison.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Example.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Thms

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune

open SeaOfNodes.Loop.MLIR.CF (model)
open Diamond.MLIR.CF.Example (num zero)
open Example (arities carry checked columns mask plan probeBank projected refusesUsed runCF runCFEdge runRVSDG
  runSource source)

example : mask.rename zero = none := rfl
example : arities = (6, some 6) := rfl
example : refusesUsed = (true, true) := rfl
example : columns = [(3, 41, some 7), (2, 42, some 6), (4, 43, some 10)] := by
  unfold columns Example.probe
  simp only [Numbered.merge_run]
  rfl

private def postOuter (old : Blocks.Bank (regs := Diamond.MLIR.CF.Example.regs) model) :=
  (source 1).body.eval model old

private def selectedFrame (old : Blocks.Bank (regs := Diamond.MLIR.CF.Example.regs) model) :=
  MLIR.CF.mergeFrame plan.header plan.join carry mask (out := num)
    (incoming plan mask model old (plan.selected model old))

example : runCFEdge 3 ((source 2).body.eval model (postOuter (probeBank 3))) =
    .inl (selectedFrame (probeBank 3)) := rfl
example : runCFEdge 2 (postOuter (probeBank 2)) = .inl (selectedFrame (probeBank 2)) := rfl
example : runCFEdge 4 (postOuter (probeBank 1)) = .inl (selectedFrame (probeBank 1)) := rfl

example :
    ((checked.headerBank model (incoming plan mask model (probeBank 2) .innerFalse)).get zero).toNat = 0 := by
  rw [incoming_reconstruct]
  rfl

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

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune
