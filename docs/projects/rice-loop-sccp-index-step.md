# Locate SCCP notifications from the popped job

`Split.Index.runSteps` uses `Index.stepLocal`. A Φ pop publishes exactly
one typed destination. The step compares that fact once and shares the answer
across the Φ, control, and result notifications. If the fact changed and
feedback is enabled with unchanged marks, it reads the field's reverse-index
bucket. A control pop writes edge marks. A result pop writes the result fact.
Both leave the carried bank unchanged. A change to the entry or feedback
mark still wakes all Φ destinations.
[Implementation](../../Silmaril/SSA/SeaOfNodes/Loop/SCCP/Worklist/Split/Index/Defs.lean)

The reference control and result watches store the whole bank when their
entry or exit mark is enabled. Each wakes on a toggle of its own mark, or on
any carried change while its mark stays enabled. The specialized pop computes
those same answers from the marks and the one write. A field can wake an
active watch even when the guard or result wire does not read that field.
`Index.wake` still compares whole banks for arbitrary assignment pairs, and
`Index.step` remains its reference pop.

`Index.gatedWatchesAfter_eq` checks both watch calculations.
`Index.stepLocal_eq` checks the complete assignment and pending queue, and
`Index.runSteps_eq_step` checks every budget including the visit trace.
The existing solver theorems prove that the queue drains and the full
assignment equals the simultaneous solution.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Loop/SCCP/Worklist/Split/Index/Thms.lean)

## Run the example

```lean
import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Index.Step.Example.Defs

open Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Index.Step.Example

#eval noOp
-- (true, (constant true, constant 255), [result], [phi 1])

#eval transitiveWake
-- (true, (constant true, constant 255), [control, phi 0, phi 1], [phi 1])

#eval feedbackActivation
-- (true, (constant true, constant 255), [phi 1, phi 0], [control])

#eval activeWatches
-- (true, (constant true, constant 255), [control, phi 0, phi 1, result], [phi 1])

#eval exitOnlyWatch
-- (true, (constant true, constant 255), [result], [phi 0])

#eval exitActivation
-- (true, (constant true, constant 255), [phi 1, result], [control])
```

Each report gives the feedback mark (exit mark for `exitActivation`),
Boolean and byte facts, pending queue, and visits. The Boolean feedback
reads the byte through two producers.
Publishing the byte from bottom wakes both its transitive reader and its
direct self-reader. Activating feedback appends the Boolean job behind the
already pending byte job. Publishing the same byte with exit enabled also
wakes result. With only the exit watch enabled, a flag write leaves the
inactive control watch quiet. It wakes result even though its wire reads
the byte. Marking exit on a control pop queues result behind the pending
byte job while the bank stays unchanged.
[Regressions](../../Silmaril/Proofs/SSA/SeaOfNodes/Loop/SCCP/Worklist/Split/Index/Step/Regression.lean)

Click's *Combining Analyses, Combining Optimizations*, §3.5 (printed p. 25),
requeues users of a changed variable. This step uses the known destination
of a single equation pop in the current pure single-loop profile.
[Reverse index](rice-loop-sccp-index.md) · [Rice dissertation](https://hdl.handle.net/1911/16807)
