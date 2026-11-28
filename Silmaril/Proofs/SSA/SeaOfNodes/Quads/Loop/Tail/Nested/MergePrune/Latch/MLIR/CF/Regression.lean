module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF.Comparison.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF.Example.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Numbered.Thms

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF

open SeaOfNodes.Loop.MLIR.CF (model)
open Diamond.MLIR.CF.Example (count decrement input num regs)
open Latch.Example (carry columns mask plan probeBank projected refusesUsed runRVSDG runSource source)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF.Example (atLatch cut incomingArities latchArity runCF runPredecessor runSite)

example : incomingArities = [some 5, some 5, some 5] := rfl
example : latchArity = some 5 := rfl
example : mask.rename decrement = none := rfl
example : atLatch.rename decrement = none := rfl
example : refusesUsed = (true, true, true, true) := rfl
example : (Split.check plan Latch.Example.checked (Latch.Example.dropSlot count.index)).isNone = true := rfl
example : columns = [(3, 41, some 7), (2, 42, some 6), (4, 43, some 10)] := by
  unfold columns Latch.Example.probe
  simp only [MergePrune.Numbered.merge_run]
  rfl

private def first := (source 0).body.eval model input
private def incomingBank (old : Blocks.Bank (regs := regs) model) :=
  (plan.pathQuads (plan.selected model old)).eval model old
private def mergeOutput (old : Blocks.Bank (regs := regs) model) :=
  (source 5).body.eval model (incomingBank old)
private def next (old : Blocks.Bank (regs := regs) model) :=
  (source 6).body.eval model (mergeOutput old)

private def second := next first
private def third := next second

example : [first, second, third].map (fun old => (plan.predecessor (plan.selected model old)).val) = [3, 2, 4] := rfl

private def mergeInput (old : Blocks.Bank (regs := regs) model) :=
  mergeFrame (carry := carry) (atLatch := atLatch) plan (mask.project (incomingBank old))
private def latchInput (old : Blocks.Bank (regs := regs) model) :=
  latchFrame (carry := carry) (merge := mask) plan (atLatch.project (mergeOutput old))

example : runPredecessor first = .inl (mergeInput first) := rfl
example : runPredecessor second = .inl (mergeInput second) := rfl
example : runPredecessor third = .inl (mergeInput third) := rfl

example : runSite (mergeInput first) = .inl (latchInput first) := rfl
example : runSite (mergeInput second) = .inl (latchInput second) := rfl
example : runSite (mergeInput third) = .inl (latchInput third) := rfl

example : runSite (latchInput first) =
    .inl (headerFrame (merge := mask) (atLatch := atLatch) plan (carry.project second)) := rfl
example : runSite (latchInput second) =
    .inl (headerFrame (merge := mask) (atLatch := atLatch) plan (carry.project third)) := rfl
example : runSite (latchInput third) =
    .inl (exitFrame (carry := carry) (merge := mask) (atLatch := atLatch) plan
      (16 : SeaOfNodes.MLIR.Word Diamond.MLIR.CF.Example.width)) := rfl

example : (runSource 14, runCF 15, runRVSDG 3) = (some 16, some 16, some 16) := by
  have cf : runCF 15 = some 16 := by unfold runCF; rw [lower_run]; rfl
  have rv : runRVSDG 3 = some 16 := by unfold runRVSDG; rw [Latch.Numbered.lower_run]; rfl
  rw [cf, rv]
  rfl

example : runCF 14 = none := by
  unfold runCF
  rw [lower_run]
  rfl

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF
