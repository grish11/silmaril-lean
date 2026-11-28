# Watch the guard and result operands in the loop SCCP FIFO

`Split.OperandWatches.build (Split.Index.build graph)` prepares typed
carried support for the guard and result. Pass the result to
`OperandWatches.run model input watches` to inspect the queue and visits,
or to `OperandWatches.solve model input watches` for the final assignment.
The support follows the ranked header producers transitively. Captures
are fixed throughout a run.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Loop/SCCP/Worklist/Split/OperandWatches/Defs.lean)

A pop reuses the indexed Φ notifications and the one typed write comparison.
While its mark stays enabled, a control or result watch wakes only if the changed destination
belongs to its operand support. A toggle of the entry or exit mark wakes
its watch independently of carried writes. Each new job joins the existing
FIFO in the usual control, Φ destination, result order. A write inside
the syntactic support can still wake a job whose right-hand side stays equal.

`control_eq_of_quiet` and `result_eq_of_quiet` prove that a quiet watch's
right-hand side stays equal across the pop. The existing FIFO proof uses
this property to maintain that every absent equation is satisfied. The
same finite-height budget drains the queue and `solve_eq_simultaneous`
compares the entire assignment, including the edge marks, every carried
fact and the result. The opt-in schedule can have different intermediate
queues and visits. The reference and exact-trace indexed APIs keep their
whole-bank wake behavior.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Loop/SCCP/Worklist/Split/OperandWatches/Thms.lean)

## Run the example

```lean
import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.OperandWatches.Example.Defs

open Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.OperandWatches.Example

#eval skippedFlag      -- ([control, result], [])
#eval resultReadsByte  -- [phi 0, phi 1, result]
#eval guardReadsByte   -- [control, phi 1]
#eval exitActivation   -- [phi 1, result]
#eval solveReport      -- ([], true, false, (constant true, constant 255), bottom)
```

In `skippedFlag`, the carried Boolean changes while both watches are active.
The guard reads a captured Boolean, and the result reads the byte. The
first queue is from the whole-bank watcher and the second is from the
operand watcher. Writing the byte wakes its relevant result and Φ
readers. The other fixture has a transitive byte read in its guard.
Activating exit queues the result behind a pending Φ with no carried
write. The final report gives the drained queue, feedback and exit marks,
both carried facts, and the result.
[Checked regressions](../../Silmaril/Proofs/SSA/SeaOfNodes/Loop/SCCP/Worklist/Split/OperandWatches/Regression.lean)

Click's *Combining Analyses, Combining Optimizations*, §3.5 (printed p. 25),
requeues users of changed variables. This solver applies that rule to the
guard and result of the existing pure single-loop profile.
[Indexed FIFO](rice-loop-sccp-index-step.md) · [Rice dissertation](https://hdl.handle.net/1911/16807)
