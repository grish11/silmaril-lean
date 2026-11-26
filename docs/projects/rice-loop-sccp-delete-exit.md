# Delete the unreachable exit of a typed MLIR loop

`Loop.SCCP.DeleteExit.rewrite` consumes the result of
`Loop.SCCP.Prune.rewrite`. In the feedback-only case, the cleanup checks
that the entry and header each end in a direct branch to the header.
It reuses their producer bindings and exact typed operand lists. The new
label type has just the header constructor, so the old exit block is
absent from the CFG. The header keeps its original block argument types
and ordering.

The exit-only case returns `.kept cfg` with the original exit block and
its incoming edge. Both-marked and neither-marked cases return `none`,
leaving the original CFG available to the caller. The dispatcher and
branch-specific pruning APIs retain their behavior.
[Unified pruning](rice-loop-sccp-prune.md)

The cleanup is scoped to the pure, fixed-width carried-bank profile
with one returned word. `delete_feedback` identifies the surviving
entry and header syntax and their original argument lists.
`header_eval` compares the successor frame after embedding its label,
with the same payload and order. `runFrom_eq` compares execution
from a retained header frame at every budget. `rewrite_run_eq`
and `rewrite_denotePart_eq` compose deletion and pruning on covered
inputs, including undefined native partial returns.
[API](../../Silmaril/SSA/SeaOfNodes/Loop/SCCP/DeleteExit/Thms.lean) ·
[Regressions](../../Silmaril/Proofs/SSA/SeaOfNodes/Loop/SCCP/DeleteExit/Regression.lean)

## Example

```lean
import Silmaril.SSA.SeaOfNodes.Loop.SCCP.DeleteExit.Example.Defs

open Silmaril.SSA.SeaOfNodes.Loop.SCCP.DeleteExit.Example

#eval run (.constant 0) 8 0  -- some (true, none)
#eval run (.constant 1) 3 1  -- some (false, some 300)
#eval run .overdefined 8 0   -- none
#eval run .bottom 8 0        -- none
#eval refusesVarying         -- true
```

The Boolean records actual block deletion. The mixed-width bank starts
at `(1, 300, 4)` and feeds back `(4, 302, 2)` with flag 0. Flag 1
retains the exit and returns 300. An outer `none` is refusal. A `none`
inside the pair means budget exhaustion.

## Rice source

Click's *Combining Analyses, Combining Optimizations* §3.6 (printed
p. 26) describes identifying code with no incoming executable jump.
§3.7 combines that analysis with constant propagation, and §3.8.1
(pp. 33–34) describes reconstructing the program and dropping unreachable
code. This slice implements the deletion of one known exit block after
the typed tail branch has been specialized. [Rice dissertation](https://hdl.handle.net/1911/16807)
