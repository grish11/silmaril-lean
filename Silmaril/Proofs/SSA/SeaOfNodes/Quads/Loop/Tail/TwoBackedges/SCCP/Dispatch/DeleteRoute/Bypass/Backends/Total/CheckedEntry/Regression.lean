module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.CheckedEntry.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.Observation.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.CheckedEntry.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.Observation.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.CheckedEntry

open Bypass.MLIR.CF.Example (entry facts looping ports program width)
open Backends.Example (stoppingFacts)
open Total.Example (bothRoutes)
open Total.Observation.Example (report)
open SeaOfNodes.Diamond.SCCP (Fact)
open SeaOfNodes.Loop.SCCP (decideTupleCovers)
open SeaOfNodes.MLIR (Word)
open RVSDG (Tuple)

private def cached := prepare program (facts (.constant ⟨true⟩))
private def incompatible := dispatch cached (entry true false)

#guard report cached.outcome (entry true false) 1 = ((5, 5, 1), (some 7, some 99, some 99))
#guard (match incompatible with | .inputIncompatible _ => true | _ => false)
#guard
  let run := incompatible.execution
  let fuel := run.budgets 1
  (fuel.source.blocks, fuel.cf.blocks, fuel.theta.activations,
    run.runCF (entry true false) fuel.cf, run.runNumbered (entry true false) fuel.theta) =
    (5, 6, 1, some 7, some 7)

example : incompatible = .inputIncompatible (emitOriginal program) := rfl

example : incompatible.execution.cfPart (entry true false) = Part.some (7 : Word width) ∧
    incompatible.execution.numberedPart (entry true false) = Part.some (7 : Word width) := by
  have source : sourcePart program (entry true false) = Part.some (7 : Word width) :=
    Part.eq_some_iff.mpr (mem_sourcePart_iff.mpr ⟨⟨5⟩, rfl⟩)
  simpa only [source, incompatible] using (dispatch_correct cached (entry true false)).part_eq

example : dispatch cached (entry true true) = .reused cached.outcome := rfl
#guard report cached.outcome (entry true true) 1 = ((5, 5, 1), (some 99, some 99, some 99))

private def both := prepare bothRoutes (facts .overdefined)
private def neither := prepare program stoppingFacts

#guard (match both.outcome with | .twoLive _ => true | _ => false)
#guard (match neither.outcome with | .neitherMarked _ => true | _ => false)
example : dispatch both (entry true true) = .reused both.outcome := rfl
example : dispatch neither (entry true true) = .reused neither.outcome := rfl

#guard
  let run := (CheckedEntry.compile bothRoutes (facts .overdefined) (entry true true)).execution
  let fuel := run.budgets 2
  (run.runCF (entry true true) fuel.cf, run.runNumbered (entry true true) fuel.theta) =
    (some 198, some 198)
#guard
  let run := (dispatch neither (entry true true)).execution
  let fuel := run.budgets 1
  (run.runCF (entry true true) fuel.cf, run.runNumbered (entry true true) fuel.theta) =
    (some 99, some 99)

-- The final word can fail coverage even with the selector covered.
private def wrongWord : Tuple (Fact Word) ports :=
  .cons .overdefined (.cons (.constant ⟨true⟩) (.cons (.constant (8 : Word width)) .nil))

#guard !(@decide _ (decideTupleCovers wrongWord (entry true true)))
#guard !(@decide _ (decideTupleCovers (facts .bottom) (entry true true)))
#guard (@decide _ (decideTupleCovers (facts .overdefined) (entry false false)))
#guard !(@decide _ (decideTupleCovers stoppingFacts (entry true true)))

-- An incompatible selector on a nonreturning loop still yields exhaustion.
#guard
  let checked := CheckedEntry.compile looping (facts (.constant ⟨true⟩)) (entry true false)
  let run := checked.execution
  let fuel := run.budgets 5
  (match checked with | .inputIncompatible _ => true | _ => false) &&
    (runSource looping (entry true false) fuel.source).isNone &&
    (run.runCF (entry true false) fuel.cf).isNone &&
    (run.runNumbered (entry true false) fuel.theta).isNone

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.CheckedEntry
