# Schedule individual typed Φ destinations

`Loop.SCCP.Worklist.Phi.step` pops one numbered destination of a native
carried bank, computes its typed fact, and updates only that coordinate.
`wake` compares each destination's watched inputs and appends changed
jobs that are absent from the queue. Existing pending jobs keep their
order. The entry mark gates the entry value. The backedge mark gates
the feedback dependency.

For an argument wire the job watches that wire's abstract fact. If it
reads a captured argument, the fact is fixed for that solve. If it reads
a carried argument, changes to other carried fields leave it alone.
For a producer result the job watches the carried arguments in its
[transitive operand support](rice-loop-sccp-phi-support.md) and uses
the existing abstract producer evaluator when popped.

`evaluate_eq` and `update_eq` identify a visit with the same coordinate
of the simultaneous transfer on its pre-pop snapshot.
`mem_wake_iff`, `wake_nodup`, and `step_stable` certify the local
queue behavior, including re-enqueue after a change. `write_comm`
allows publishing different destinations prepared from a common
snapshot in either order. Re-evaluating after a publication is a
different worklist visit and may read a new assignment. Neither
operation changes the native loop's simultaneous latch semantics.
[API](../../Silmaril/SSA/SeaOfNodes/Loop/SCCP/Worklist/Phi/Thms.lean)

## Example

```lean
import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi.Example.Defs

open Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi.Example

#eval widening []
#eval widening [(1 : Fin 2)]
#eval feedbackReads
```

Both widening calls report the unchanged flag `constant true`, the
widened byte `overdefined`, and pending destinations `[1]`. The flag
job is absent, and an already pending word job stays unique.
The cross-field example reports `(constant true, constant 0)` for
a frozen snapshot and `(constant true, constant 1)` when the second
equation is re-evaluated after writing the first.
[Checked regressions](../../Silmaril/Proofs/SSA/SeaOfNodes/Loop/SCCP/Worklist/Phi/Regression.lean)

## Rice source and scope

Click's *Combining Analyses, Combining Optimizations* §3.5,
printed p. 25, updates one equation variable and requeues equations
that read the changed variable. This increment splits the Φ equation
into typed destinations and supplies the local transfer and pending
invariant used by the [integrated mixed FIFO](rice-loop-sccp-split-fifo.md).
The step scans Φ destinations when waking jobs. Reverse notification
indexing, general CFG SCCP, and Rice's complexity bound are outside
this profile.
[Rice dissertation](https://hdl.handle.net/1911/16807) ·
[Existing cyclic solver](rice-loop-sccp-worklist.md)
