# Run cyclic SCCP with individual typed Φ jobs

Import `Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Thms`.
`Loop.SCCP.Worklist.Split.run model graph facts` reports the final
assignment, pending queue, and FIFO visits. `Split.solve` returns the
assignment alone. Control and result use the existing worklist equations.
Each Φ job updates its own typed coordinate using the checked
[`Phi.update`](rice-loop-sccp-phi-jobs.md). The original three-job API
remains available.

After a pop, the queue keeps its pending prefix and appends jobs with
changed watched inputs in control, numbered Φ, result order. Entry
enables the entry Φ operands and control's bank read. Enabling feedback
adds each destination's feedback watch. Enabling exit adds only result's
bank watch. Direct wires watch their typed values, and producer-fed jobs
conservatively watch the whole active bank.

`step_stable` keeps every unqueued equation satisfied. On a strict
assignment ascent, the remaining rank pays for at most the number of
jobs that can be appended. Without an ascent, the pop shortens the queue.
`run_drains` and `solve_eq_simultaneous` give termination and equality
of the whole assignment, including occurrence marks, all Φ fields,
and the result. The proof uses monotonicity and the least-fixed-point
law. One pop reads the assignment left by the previous pop. The
native simultaneous feedback semantics stays in the original equations
and coverage theorem.
[Public API](../../Silmaril/SSA/SeaOfNodes/Loop/SCCP/Worklist/Split/Thms.lean)

## Example

```lean
import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Example.Defs

open Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Example
open Silmaril.SSA.SeaOfNodes.Loop.SCCP.Example.Bank (graph)

#eval (report direct true 0).2
#eval (report (graph false) true 0).2
#eval (report (graph true) false 0).2
#eval (report (graph false) true 5).2
#eval wideningWake []
#eval enableExitWake
```

The first four calls give the backedge mark, exit mark, typed flag and
byte facts, and result fact.

| Program | Backedge | Exit | Flag and byte | Result |
| --- | --- | --- | --- | --- |
| Direct feedback | yes | no | constant true, constant 0 | bottom |
| Incrementing feedback | yes | yes | constant true, overdefined | overdefined |
| Cross-field feedback | yes | yes | overdefined, overdefined | overdefined |
| No feedback | no | yes | constant true, constant 5 | constant 6 |

The last calls report `[control, phi 1]` after widening the byte and
`[result]` after enabling only exit. The regressions also check that
an already pending Φ job keeps its position and that a second
cross-field pop can use a fact published by the first.
[Checked regressions](../../Silmaril/Proofs/SSA/SeaOfNodes/Loop/SCCP/Worklist/Split/Regression.lean)

## Rice source and scope

Click's *Combining Analyses, Combining Optimizations* §3.5, printed
p. 25, computes one equation variable and requeues equations that use
it. This solver instantiates that pattern for the typed pure single-loop
profile in the dual order. Each wake scans the finite job roster.
Producer-fed dependencies stay conservative. The proof and traces
cover the carried-bank loop. General CFG SCCP, transitive producer
def-use indexing, and the dissertation's complexity bound are outside
this slice.
[Rice dissertation](https://hdl.handle.net/1911/16807) ·
[Original FIFO](rice-loop-sccp-worklist.md)
