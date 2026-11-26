# Reverse Φ notifications in the mixed SCCP FIFO

Build `Split.Index.build graph` once and pass it to
`Split.Index.run model input index` or `Split.Index.solve model input index`.
The index stores the Φ destinations that read each typed carried coordinate.
Construction shares the ranked producer support table across destinations.
For arbitrary state pairs, `Index.wake` compares carried facts and unions
the reader sets for changed coordinates when feedback is enabled. Changes to the entry or
feedback mark notify every Φ, since both marks are part of every Φ watch.
Control and result keep their original entry- and exit-gated whole-bank watches.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Loop/SCCP/Worklist/Split/Index/Defs.lean)

The notifier sorts the union by destination and uses the existing FIFO
insertion. Pending jobs retain their order. New jobs join in control,
destination, result order, and a job read through multiple changed inputs
joins once. The equality `Index.wake_eq` holds for any old and new
assignments and any pending prefix. `Index.step_eq` and `Index.runSteps_eq`
extend it to a pop and to every budget, including the visits.
`Index.run_drains` and `Index.solve_eq_simultaneous` reuse the
reference FIFO's termination and full-assignment proof.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Loop/SCCP/Worklist/Split/Index/Thms.lean)

## Run the example

```lean
import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Index.Example.Defs

open Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Index.Example

#eval readerReport         -- [[1], [0, 1]]
#eval flagOnly             -- [control, phi 1, result]
#eval multiTrigger         -- [control, phi 0, phi 1, result]
#eval prequeued            -- [phi 1, control, phi 0, result]
#eval gated                -- [control, result]
#eval activation           -- [phi 0, phi 1]
#eval activationAndFields  -- [result, phi 0, control, phi 1]
#eval solveReport          -- (true, true, (overdefined, overdefined), overdefined)
```

The byte Φ uses the old Boolean and byte. The Boolean Φ uses the old
byte. Widening both fields finds the byte Φ twice, but it is queued only
once. A prequeued byte job stays in front of newly awakened jobs. With
feedback disabled, widening the same fields only wakes control and result.
The final report shows the backedge and exit marks, both carried facts, and
the exit fact. [Checked regressions](../../Silmaril/Proofs/SSA/SeaOfNodes/Loop/SCCP/Worklist/Split/Index/Regression.lean)

Click's *Combining Analyses, Combining Optimizations*, §3.5 (printed p. 25),
uses variable changes to requeue users. This index applies that rule to
the typed Φ support of the pure single-loop
profile. The bounded runner uses the popped job to locate its changed
coordinate. The reference `Split` API remains available for comparison.
[Typed Φ support](rice-loop-sccp-phi-support.md) · [Specialized pop](rice-loop-sccp-index-step.md) · [Rice dissertation](https://hdl.handle.net/1911/16807)
