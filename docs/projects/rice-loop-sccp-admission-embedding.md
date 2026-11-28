# Guarded SCCP admission after an embedding

The step-labelled refusal from the two-contraction example still refuses
when compiled in one shot. The first map, second map, and composite all
pass the written-port checks. The first and one-shot fact intersections both succeed.
The FIFO rows explain the refusal.
[Two-map lift and compiler](rice-loop-sccp-lift-composition.md)

| Checker input | Entry operands of the header comparison | Header continuation | Marked feedback | Exit |
| --- | --- | --- | --- | --- |
| Original | `7`, overdefined | Overdefined | True | Marked |
| After first contraction | `7`, `7` | False | None | Marked |
| One-shot composite | `7`, `7` | False | None | Marked |

The header uses unsigned less-than. The first contraction intersects
the old 7 with the overdefined entry fact and supplies the same read-only
slot to both operands. With `7 < 7` false, the FIFO marks the exit and
refuses singleton specialization with `neitherMarked`. The second
contraction in this fixture leaves that row unchanged.

## Exact transport for an embedding suffix

Given `first : PortMap S T` and `suffix : Embedding T U`, call
`Admission.compile_direct_eq_staged first suffix admitted`. The theorem
equates the actual one-shot `Identification.compile` and
`Composition.compileStaged` outcomes. On success it equates the stored
guarded MLIR CF and numbered RVSDG artifacts. On refusal it preserves the
reason. The first map can identify read-only captures, and the suffix can
permute the bank and insert unused captures. A suffix that identifies
intermediate ports lies outside this theorem.

- `pushFacts_embedding` moves each old fact to its embedded coordinate and
  gives every fresh coordinate an overdefined fact. It also preserves an
  empty intersection.
- `fifo_marks` uses the existing least-solution laws for permutation and
  weakening and the checked FIFO agreement with the simultaneous solver.
  Both feedback marks and the exit mark are unchanged.
- `admit_embedding` applies to arbitrary source quads and entry facts at
  the intermediate boundary, including cases where there is a FIFO refusal.
- `compare_embedding` specializes the existing two-typed-map comparison
  to an embedding suffix. It runs the ordinary type/map checker in both
  stages and independently for the composite. Its two final artifacts are
  exactly the one-shot result. Any refusal is reported at the first call.

[Public theorem statements](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/ContextEmbedding/Admission/Thms.lean)

## Run the audit and the embedded case

```lean
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Admission.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Admission.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Admission.Example
  (previousWriteChecks previousRows previousOneShotRefusal embeddingRefusals embeddedAccepted)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.LiftComposition.Example
  (compilerRefusal)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition.Example
  (run staged direct)

#eval previousWriteChecks
-- some (true, true, true)
#eval previousRows
#eval (compilerRefusal, previousOneShotRefusal)
-- The staged path reports first (checker neitherMarked), and the one-shot path reports checker neitherMarked.
#eval embeddingRefusals
#eval embeddedAccepted
-- true
#eval (run staged 65535 true, run direct 0 true)
-- Both native, CF, and numbered runs return 99.
#eval (run staged 0 false, run direct 65535 false)
-- Both native, CF, and numbered runs return 14.
```

The embedding fixture inserts an unused interior `i16` between the
predicate slots. The artifact runs use the separately established native,
CF and numbered execution bounds.
[Checked regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/ContextEmbedding/Admission/Regression.lean)
