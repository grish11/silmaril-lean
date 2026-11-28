module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Example.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF.Thms

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration

open Diamond.MLIR.CF.Example (input regs)
open SeaOfNodes.Loop.MLIR.CF (evalOp model)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Example
  (atLatch carry cf checked feedback feedbackCheck first latchCounts merge numbered plan predecessorOrder prepared projected
    refusesBeforeRescan runBody runCF runNumbered runSource second settled third)
open Blocks (Bank)

example : (refusesBeforeRescan, prepared.positions, settled) = (true, [1, 0], true) := rfl
example : SeaOfNodes.Pure.Deletion.Iteration.NoEligible prepared.final := prepared.noEligible
example : feedbackCheck = (true, true, 3, true) := rfl
example : latchCounts = ((7, 5), (7, 5)) := rfl
example : predecessorOrder = [3, 2, 4] := rfl

private theorem runBody_agrees (old : Bank (regs := regs) model) :
    runBody old = some (MergePrune.Numbered.latchPacket plan carry model (Nested.Numbered.nextBank plan model old)) :=
  numbered_activation_run plan model projected checked prepared 0 old

example : feedback = [some (1, 2, 7), some (1, 1, 8), some (0, 0, 16)] := by
  simp only [feedback, List.map_cons, List.map_nil, runBody_agrees]
  rfl

private def runPredecessor (old : Bank (regs := regs) model) :=
  let occurrence := plan.selected model old
  let frame := MLIR.CF.siteFrame plan (plan.predecessor occurrence) (MLIR.CF.predecessorBank plan old occurrence)
  (cf.block frame.label).eval evalOp (fun term env => term.eval env) (frame.args.append (encodeValues input))

private def expectedMerge (old : Bank (regs := regs) model) :=
  MLIR.CF.mergeFrame (carry := carry) (atLatch := atLatch) plan (incoming plan merge model old (plan.selected model old))

private theorem runPredecessor_agrees (old : Bank (regs := regs) model)
    (beforeLatch : plan.predecessor (plan.selected model old) ≠ plan.latch) :
    runPredecessor old = .inl (expectedMerge old) := by
  have original := MLIR.CF.selected_predecessor_frame plan projected checked input old
  unfold runPredecessor expectedMerge
  dsimp only at original ⊢
  unfold MLIR.CF.siteFrame at original ⊢
  rw [ite_eq_right beforeLatch] at original ⊢
  exact original

example : runPredecessor first = .inl (expectedMerge first) := runPredecessor_agrees first (by decide)
example : runPredecessor second = .inl (expectedMerge second) := runPredecessor_agrees second (by decide)
example : runPredecessor third = .inl (expectedMerge third) := runPredecessor_agrees third (by decide)

example : (runSource 14, runCF 15, runNumbered 3) = (some 16, some 16, some 16) := by
  unfold runCF cf runNumbered numbered
  rw [cf_run, numbered_run]
  rfl

example : (runSource 13, runCF 14, runNumbered 2) = (none, none, none) := by
  unfold runCF cf runNumbered numbered
  rw [cf_run, numbered_run]
  rfl

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration
