# Emit the SCCP-pruned quad loop as numbered RVSDG

`Bypass.Numbered.compile model program facts` runs the singleton feedback
check from the dead-route rewrite and emits a numbered `NestedTheta.Graph`.
The compiler numbers the existing quad blocks with their typed reaching
versions. The same entry contract `TupleCovers facts input` supplies the
connection to the original two-route source. The checker refuses when both
feedback routes are marked.
[Entry point](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/SCCP/Dispatch/DeleteRoute/Bypass/Numbered/Defs.lean) ·
[Source bypass](rice-loop-sccp-bypass-dispatch.md)

Existing θ is post-tested and requires a body activation before it can return.
The emitted entry γ therefore runs after the preheader and first header.
Its false arm projects the original result port from the first header bank,
even at bound zero. Its true arm passes the entire first header bank to θ.
Each θ body runs the retained feedback quads and then the next header, tagging
the entire updated bank with the next header's test. `packet_run` checks that
typed packet on the actual numbered body and `lower_exit` checks the
first-header projection. The other feedback route is absent from the graph.
[θ semantics](../../Silmaril/SSA/RVSDG/NestedTheta/Defs.lean) ·
[Checked laws](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/SCCP/Dispatch/DeleteRoute/Bypass/Numbered/Thms.lean)

For a feedback limit `n`, the numbered run uses bound `n`, the original
source uses `3 * n + 2` block visits, and the bypassed source uses
`2 * n + 2`. The typed CF target uses `2 * n + 3`, including the
explicit return block. `compile_run` and `compile_cf_run` compare exact
observations at those budgets, including exhaustion. `compile_returns_iff`
and `compile_noReturn_iff` preserve and reflect finite returns and their
absence. `compile_cf_returns_iff` compares finite observations in both
targets. The numbered emitter is generic over the pure quad model. The CF
comparison uses the existing fixed-width model with a single word result.
[CF comparison](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/SCCP/Dispatch/DeleteRoute/Bypass/Numbered/Comparison/Thms.lean) ·
[Typed MLIR CF emitter](rice-loop-sccp-bypass-mlir.md)

## Run the example

```lean
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.Example
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example
  (facts program looping)
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (model)

#eval observations program true false 1    -- some (some 7, some 7, some 7)
#eval observations program true true 1     -- some (some 99, some 99, some 99)
#eval packet false                         -- some (0, false, false, 7)
#eval packet true                          -- some (0, false, true, 99)
#eval observations headerWrite false true 0 -- some (some 42, some 42, some 42)
#eval observations looping true true 9    -- some (none, none, none)
#eval (compile model program (facts .overdefined)).isNone -- true
```

Each observation lists the original result, numbered result and CF result.
The packet lists the tag, continue bit, selector and reaching byte.
The immediate exit reads `42` from the header despite the selected feedback
body's write of `99`. The continuing fixture has no finite numbered return.
[Regressions](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/SCCP/Dispatch/DeleteRoute/Bypass/Numbered/Regression.lean)

Rice §3.6, Figure 3.7 (printed p. 26), motivates the cyclic executable-edge
analysis reused by this lowering. The construction covers the checked pure
quad shape and its retained feedback occurrence.
[Rice dissertation](https://hdl.handle.net/1911/16807) ·
[Wegman–Zadeck](https://doi.org/10.1145/103135.103136)
