# Check a concrete entry before running the quad compiler's targets

Use `CheckedEntry.prepare p facts` to run the existing `Total.compile` once
and cache its result with the exact facts it used. Then call
`CheckedEntry.dispatch prepared input` for each concrete typed bank.
`CheckedEntry.compile p facts input` combines both steps for a single input.
The checked result applies to that input. Dispatch again before using a
specialization on a different input.
[Entry dispatcher](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/SCCP/Dispatch/DeleteRoute/Bypass/Backends/Total/CheckedEntry/Defs.lean)

For a singleton specialization, the dispatcher decides `TupleCovers` at
every typed input port. Overdefined covers every value, a constant covers
the equal value, and an unseen (bottom) fact covers no values. A covered
input reuses the specialized CF and numbered graphs. An uncovered input
yields `.inputIncompatible` with the original two-route graphs. An analysis
result of `.twoLive` or `.neitherMarked` already contains the original graphs
and is reused directly, even on an uncovered input.
[Typed decision procedure](../../Silmaril/SSA/SeaOfNodes/Loop/SCCP/Coverage/Defs.lean)

`CheckedEntry.dispatch_correct prepared input` needs no separate coverage
proof. On `selected.execution`, the theorem provides the matched-budget
law (`.bounded`), finite return equivalence with independently quantified
budgets (`.returns_iff`), absence of finite returns (`.noReturn_iff`), and
equality of the normalized partial returned words (`.part_eq`). For
feedback limit `n`, the budget record gives source blocks `3*n+2`,
CF blocks `2*n+3` for specialization or `3*n+3` for the original graphs,
and numbered θ activations `n`.
[Public theorem](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/SCCP/Dispatch/DeleteRoute/Bypass/Backends/Total/CheckedEntry/Thms.lean) ·
[Observation contract](rice-loop-sccp-total-observations.md)

## Run the mixed-width example

```lean
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.CheckedEntry.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.Observation.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.Observation.Example (report)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example (program entry facts)

def prepared := CheckedEntry.prepare program (facts (.constant ⟨true⟩))
def input := entry true false
def selected := CheckedEntry.dispatch prepared input

#eval report prepared.outcome input 1
-- ((5, 5, 1), some 7, some 99, some 99)

#eval match selected with
  | .inputIncompatible _ => true
  | .reused _ => false
-- true

#eval
  let runner := selected.execution
  let fuel := runner.budgets 1
  (runner.runCF input fuel.cf, runner.runNumbered input fuel.theta)
-- (some 7#8, some 7#8)

example : selected.execution.cfPart input = sourcePart program input :=
  (CheckedEntry.dispatch_correct prepared input).part_eq.1
```

The regressions also exercise a compatible specialization, both analysis
fallbacks, and bounded exhaustion on a nonreturning input. This dispatcher
is for the fixed pure two-route quad profile. It checks the input contract
around the existing SCCP compiler.
[Checked regressions](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/SCCP/Dispatch/DeleteRoute/Bypass/Backends/Total/CheckedEntry/Regression.lean) ·
[Rice and Wegman–Zadeck correspondence](rice-loop-sccp-two-route-worklist.md#source-correspondence)
