# A noninjective suffix can change FIFO admission

The pure five-block example in `Admission.Noninjective` passes the write
checks for the first map, the second map, and their composite. Both maps
identify read-only word slots. The first compiler emits guarded MLIR CF
and numbered RVSDG and selects true feedback. The second compiler and the
independent one-shot compiler both refuse with `neitherMarked`.
`LiftComposition.compare` labels this as a second-call refusal. The
earlier two-contraction example stopped at the first call.
[Public checked statements](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/ContextEmbedding/Admission/Noninjective/Thms.lean) ·
[Earlier refusal](rice-loop-sccp-admission-embedding.md)

The preheader writes scratch to 1. The header multiplies scratch by a
read-only multiplier, then tests unsigned `threshold < scratch`. Each
feedback writes scratch to zero. The abstract entry selector is true
throughout the example.

- The first intersection combines seed 7 with the overdefined threshold.
  The threshold is now 7, and the multiplier stays overdefined. The
  true feedback row contributes zero to the scratch Φ, which also
  receives the entry value 1.
- The second intersection combines the seed/threshold slot with the
  overdefined multiplier. Both now read 7. The entry scratch stays 1
  because the header computes `7 < 7 * 1`, marks exit, and enables
  neither feedback row. The staged and direct final intersections return
  exactly the same typed fact tuple.

| Actual drained FIFO row | Scratch Φ | Guard left | Guard right | Continuation | Marked occurrences |
| --- | --- | --- | --- | --- | --- |
| Original | Overdefined | Overdefined | Overdefined | Overdefined | Entry, true feedback, exit |
| First | Overdefined | 7 | Overdefined | Overdefined | Entry, true feedback, exit |
| Second | 1 | 7 | 7 | False | Entry, exit |
| One shot | 1 | 7 | 7 | False | Entry, exit |

`compiler_differential` supplies the original admitted program and its
actual first emission, with exact equations for both final refusals.
`intersections_exact` and `rows_exact` are kernel-checked equalities
for the fact blocks and the executable rows. This establishes that
first-stage acceptance alone does not imply final acceptance for a
noninjective suffix. The agreement theorem for an embedding suffix
continues to cover permutations and unused insertions.

## Run the example

The three runs below use actual emitted CF and numbered RVSDG from the
first compilation, with 12 CF block visits and a numbered θ budget of 3.
Multiplier 7 takes the immediate exit. Multiplier 8 takes a feedback,
resets scratch, and exits with zero. Setting the selector false in the
last run exercises the guarded fallback.

```lean
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Admission.Noninjective.Thms

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Admission.Noninjective

#eval writeChecks
-- (true, true, true)
#check intersections_exact
#eval rows
#eval outcomes
-- First: ok true. Staged: second (checker neitherMarked). One shot: checker neitherMarked.
#eval (runIntermediate 7 true, runIntermediate 8 true, runIntermediate 8 false)
-- (some (some 7, some 7), some (some 0, some 0), some (some 0, some 0))
```
