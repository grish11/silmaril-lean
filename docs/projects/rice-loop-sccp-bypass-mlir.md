# Emit the SCCP-pruned quad loop as typed MLIR CF

`SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.compile program facts` runs the
existing singleton feedback check and emits a typed `MLIR.CF.Cfg`. It refuses
when both feedback occurrences are marked. Execution guarantees require
`TupleCovers facts input`, relating the concrete entry bank to the facts.
The CF emitter takes the three-block bypassed source directly. Its external
entry runs the original preheader. The header tests the post-header bank and
either sends that entire bank to the retained feedback block or sends the
return word to the explicit CF return block. The feedback block sends its
entire updated bank back to the header. The source tests before feedback
assignments, whereas the existing tail-tested profile tests after latch
assignments.
[Source bypass](rice-loop-sccp-bypass-dispatch.md) ·
[Emitter and admission API](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/SCCP/Dispatch/DeleteRoute/Bypass/MLIR/CF/Defs.lean)

`compile_returns_iff` preserves and reflects each finite return value against
the original two-route source. `compile_diverges_iff` relates all-budget CF
exhaustion to absence of a finite original return. A covered execution taking
`n` feedback steps needs `3 * n + 2` original block visits or
`2 * n + 3` CF visits, including the explicit CF return. `compile_run`
compares observations at those respective budgets for any feedback limit,
including exhaustion before a return or on a nonreturning execution.
`entry_frame`, `header_frame` and `feedback_frame` give the exact emitted jump
arguments.
[Checked laws](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/SCCP/Dispatch/DeleteRoute/Bypass/MLIR/CF/Thms.lean)

## Run the example

```lean
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example

#eval observations program true false 5 5  -- some (some 7, some 7)
#eval observations program true true 5 5   -- some (some 99, some 99)
#eval reachingBank true                    -- some (false, true, 99)
#eval observations program false true 2 3  -- some (some 7, some 7)
#eval observations looping true true 29 21 -- some (none, none)
#eval (compile program (facts .overdefined)).isNone  -- true
```

The observation pair lists the original result first and the CF result
second. The reaching bank lists the new continue bit, unchanged selector
and new byte. An immediate exit on the true-route contract returns `7`
before the feedback assignment that would write `99`.
[Checked regressions](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/SCCP/Dispatch/DeleteRoute/Bypass/MLIR/CF/Regression.lean)

Rice §3.6, Figure 3.7 (printed p. 26), supplies the cyclic reachability
motivation. The backend here is the repository's pure, fixed-width
`arith`/CF interpreter with a single result word. The check is specific to
the five-block source and its certified compact form.
[Rice dissertation](https://hdl.handle.net/1911/16807) ·
[Wegman–Zadeck](https://doi.org/10.1145/103135.103136)
