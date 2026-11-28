module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Numbered.DeadProducer.Comparison.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Numbered.DeadProducer.Example.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Numbered.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Numbered.DeadProducer

open Diamond.MLIR.CF.Example (regs)
open SeaOfNodes.Loop.MLIR.CF (model)
open Latch.MLIR.CF.DeadProducer.Example
  (carry cut keptResult plan projected refuses runCF runRVSDG runSource shortened)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Numbered.DeadProducer.Example
  (feedback first latchTests predecessorOrder runBody runNumbered second third)
open Blocks (Bank)

example : latchTests = ([true, false, false, false, true], [false, false, false, true]) := rfl
example : refuses = (true, true, true) := rfl
example : shortened.candidate = .here := rfl
example : predecessorOrder = [3, 2, 4] := rfl

private theorem runBody_agrees (old : Bank (regs := regs) model) :
    runBody old = some (MergePrune.Numbered.latchPacket plan carry model (Nested.Numbered.nextBank plan model old)) := by
  unfold runBody
  rw [← RVSDG.NestedTheta.Graph.run_toTerm, RVSDG.NestedTheta.Term.toTerm_toGraph, activation_run]

-- Both feedback tuples, including their untouched fields, are simultaneous.
private theorem firstFeedback :
    runBody first = some (RVSDG.Theta.bodyResult (Join.model model) true (carry.project second)) := by
  rw [runBody_agrees]
  rfl

private theorem secondFeedback :
    runBody second = some (RVSDG.Theta.bodyResult (Join.model model) true (carry.project third)) := by
  rw [runBody_agrees]
  rfl

private theorem exitPacket : runBody third = some (RVSDG.Theta.bodyResult (Join.model model) false
    (carry.project (Nested.Numbered.nextBank plan model third))) := by
  rw [runBody_agrees]
  rfl

example : feedback = [some (1, 2, 7), some (1, 1, 8), some (0, 0, 16)] := by
  simp only [feedback, List.map_cons, List.map_nil, firstFeedback, secondFeedback, exitPacket]
  rfl

example : (runSource 14, runCF 15, runRVSDG 3, runNumbered 3) = (some 16, some 16, some 16, some 16) := by
  have cf : runCF 15 = some 16 := by unfold runCF; rw [MLIR.CF.DeadProducer.lower_run]; rfl
  have before : runRVSDG 3 = some 16 := by unfold runRVSDG; rw [Numbered.lower_run]; rfl
  have after : runNumbered 3 = some 16 := by unfold runNumbered Example.numbered; rw [run_agrees]; exact before
  rw [cf, before, after]
  rfl

example : (runSource 13, runCF 14, runRVSDG 2, runNumbered 2) = (none, none, none, none) := by
  have cf : runCF 14 = none := by unfold runCF; rw [MLIR.CF.DeadProducer.lower_run]; rfl
  have before : runRVSDG 2 = none := by unfold runRVSDG; rw [Numbered.lower_run]; rfl
  have after : runNumbered 2 = none := by unfold runNumbered Example.numbered; rw [run_agrees]; exact before
  rw [cf, before, after]
  rfl

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Numbered.DeadProducer
