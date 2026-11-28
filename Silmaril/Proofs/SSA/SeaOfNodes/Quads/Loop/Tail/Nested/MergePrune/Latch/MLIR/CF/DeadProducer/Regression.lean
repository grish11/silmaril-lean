module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF.DeadProducer.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF.DeadProducer.Example.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Split.DeadProducer.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Numbered.Thms

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF.DeadProducer

open Diamond.MLIR.CF.Example (num regs input)
open SeaOfNodes.Loop.MLIR.CF (model)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF.DeadProducer.Example
  (atLatch carry latchCounts mask plan refuses runCF runPredecessor runRVSDG runSite runSource shortened source)

example : latchCounts = (5, 4) := rfl
example : refuses = (true, true, true) := rfl
example : shortened.candidate = .here := rfl

private def incomingBank (old : Blocks.Bank (regs := regs) model) :=
  (plan.pathQuads (plan.selected model old)).eval model old
private def mergeOutput (old : Blocks.Bank (regs := regs) model) :=
  (source 5).body.eval model (incomingBank old)
private def next (old : Blocks.Bank (regs := regs) model) :=
  (source 6).body.eval model (mergeOutput old)

private def first := (source 0).body.eval model input
private def second := next first
private def third := next second

example : [first, second, third].map (fun old => (plan.predecessor (plan.selected model old)).val) = [3, 2, 4] := rfl

private def mergeInput (old : Blocks.Bank (regs := regs) model) :=
  CF.mergeFrame (carry := carry) (atLatch := atLatch) plan (mask.project (incomingBank old))

example : runPredecessor first = .inl (mergeInput first) := rfl
example : runPredecessor second = .inl (mergeInput second) := rfl
example : runPredecessor third = .inl (mergeInput third) := rfl

private def latchInput (old : Blocks.Bank (regs := regs) model) :=
  CF.latchFrame (carry := carry) (merge := mask) plan (atLatch.project (mergeOutput old))

example : runSite (latchInput first) =
    .inl (CF.headerFrame (merge := mask) (atLatch := atLatch) plan (carry.project second)) := rfl
example : runSite (latchInput second) =
    .inl (CF.headerFrame (merge := mask) (atLatch := atLatch) plan (carry.project third)) := rfl
example : runSite (latchInput third) =
    .inl (CF.exitFrame (carry := carry) (merge := mask) (atLatch := atLatch) plan
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

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF.DeadProducer
