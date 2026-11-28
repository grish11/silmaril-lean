# Observe any result of the total quad compiler

`Total.compile_correct` takes an equation `Total.compile p facts = outcome`
and a proof of `outcome.Compatible facts input`. It returns `Correct outcome input`
for the actual artifacts in that outcome. The theorem handles dispatch admission
and all three tags internally. `Outcome.compatible_of_covers` supplies
compatibility from an existing `TupleCovers facts input` proof for any outcome.
When the result is specialized, coverage is required. Both original fallbacks
accept every typed input, even when it disagrees with the entry facts.
[Public theorem](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/SCCP/Dispatch/DeleteRoute/Bypass/Backends/Total/Observation/Thms.lean) ·
[Compiler and outcome contract](rice-loop-sccp-total-backends.md)

Pass a feedback limit `n` to `outcome.budgets n`. The returned record uses
distinct `SourceBudget`, `CFBudget`, and `ThetaBudget` types. Source block
fuel is `3 * n + 2` and θ fuel is `n`. CF block fuel is `2 * n + 3` for
specialization and `3 * n + 3` for either fallback. Use `runSource`,
`outcome.runCF` and `outcome.runNumbered` to read the single result word
from these executions.
[Budget and runner definitions](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/SCCP/Dispatch/DeleteRoute/Bypass/Backends/Total/Observation/Defs.lean)

The proof's `bounded` field compares all three runs at those respective
budgets, including exhaustion. Its `returns_iff` field compares finite
returns with independently quantified budgets. `noReturn_iff` relates
exhaustion at every target budget to absence of a finite source return.
`part_eq` compares `Part Word` observations. The CF observation projects
the actual typed CF denotation through its pure embedding, and the
numbered observation projects the existing partial semantics with total
primitives. The source observation is witnessed by a finite native run.
An undefined partial result has no finite return witness.

## Run the example

```lean
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.Observation.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.Observation.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.Observation.Example
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.Example
  (bothRoutes)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Example
  (stoppingFacts)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example
  (entry facts program)

#eval report (compile program (facts (.constant ⟨true⟩))) (entry true true) 1
#eval report (compile bothRoutes (facts .overdefined)) (entry true true) 2
#eval report (compile program stoppingFacts) (entry true true) 1

example (outcome : Outcome program) (compiled : compile program stoppingFacts = outcome)
    (compatible : outcome.Compatible stoppingFacts (entry true true)) :
    outcome.runCF (entry true true) (outcome.budgets 1).cf =
      runSource program (entry true true) (outcome.budgets 1).source := by
  exact ((compile_correct compiled compatible).bounded 1).1
```

The reports list budgets and then observations in source, CF, numbered
order. The specialized fixture gives `(5, 5, 1)` and three returns of
`99`. The two-live fixture gives `(8, 9, 2)` and three returns of `198`.
The neither-marked fixture gives `(5, 6, 1)` and three returns of `99`,
although the concrete header continues and the entry fact says it stops.
The refutation regression also uses a false selector with a true-route
specialization. In that case the raw target returns `99` and the source
returns `7`, so the compatibility hypothesis is material.
[Checked regressions](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/SCCP/Dispatch/DeleteRoute/Bypass/Backends/Total/Observation/Regression.lean) ·
[Rice and Wegman–Zadeck correspondence](rice-loop-sccp-two-route-worklist.md#source-correspondence)
