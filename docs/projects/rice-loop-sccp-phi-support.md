# Watch the carried operands of producer-fed Φ jobs

`Loop.SCCP.Worklist.Phi.feedbackSupport graph job` computes a set of
typed carried coordinates for a feedback operand in the ranked pure
single-loop table. A carried input contributes its coordinate. A
captured input contributes nothing because its fact is fixed for
the run. Each producer's support is the union of its operand supports.
A nullary producer therefore has empty support.

For a producer-fed Φ job with enabled feedback, the watch keeps this
subset of the bank and fills all other coordinates with bottom.
`Support.restrictBank_eq_iff` identifies key equality with agreement
on precisely that subset. `Support.wire_agrees` and `Phi.feedback_agrees`
prove that the same shared abstract evaluator reads the original
feedback fact from the restricted bank. The proof follows typed
origins through producer order. It checks syntactic operand support,
so a primitive can still ignore an operand that the graph supplies.
[Support API](../../Silmaril/SSA/SeaOfNodes/Loop/SCCP/Worklist/Phi/Support/Thms.lean) ·
[Φ API](../../Silmaril/SSA/SeaOfNodes/Loop/SCCP/Worklist/Phi/Thms.lean)

The mixed FIFO retains its queue order, duplicate suppression, and
proof that the queue drains to the entire simultaneous solution.
The bank watch for control and result remains gated by entry and
exit respectively, and the Φ feedback watch remains gated by the
backedge mark. The watch builds the support from the ranked table
and uses the existing pointwise bank representation. Waking jobs
still scans the finite roster. This keeps the scope to the existing
pure loop and leaves reverse notification indexing separate.
[Mixed FIFO](rice-loop-sccp-split-fifo.md)

## Example

```lean
import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi.Support.Example.Defs

open Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi.Support.Example

#eval flagSupport    -- [1]
#eval wakeAfterFlag  -- [control]
#eval wakeAfterByte  -- [control, phi 0, phi 1]
#eval solveReport    -- (true, false, (constant true, constant 255), bottom)
```

The Boolean destination reads a byte through two producers. Widening
the old flag leaves that job unqueued. Widening the byte wakes the
producer-fed Boolean job and the byte's direct self-feedback job.
[Checked regressions](../../Silmaril/Proofs/SSA/SeaOfNodes/Loop/SCCP/Worklist/Phi/Support/Regression.lean)

## Rice source

Click's *Combining Analyses, Combining Optimizations*, §3.5 (printed
p. 25), requeues equations that use a changed variable. This slice
checks which carried variables the producer-fed Φ equations read
in the existing pure-loop profile. [Rice dissertation](https://hdl.handle.net/1911/16807)
