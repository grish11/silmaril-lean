# Remove the excluded feedback block from the quad loop

`SCCP.Dispatch.DeleteRoute.compact checked` consumes the singleton
dispatcher certificate and emits a typed `Tail.Source` on `Fin 4`.
`DeleteRoute.rewrite model program inputFacts` runs the checker and
returns that source when admitted. Two marked feedback routes are
refused. The existing checked tail chain places its test on the latch.
Here the test precedes the dispatcher and feedback assignments, so the
compact source keeps that header test and the original visit order.
[Checked dispatch](rice-loop-sccp-dispatch.md) ·
[Tail chain](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Chain/Defs.lean) ·
[Definitions](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/SCCP/Dispatch/DeleteRoute/Defs.lean)

The kept-block map fixes entry, header and dispatcher at indices 0, 1
and 2. Compact index 3 names the original selected block, which was 3
for true or 4 for false. Lean checks that the map is injective and its
image is exactly the complement of the excluded block. Every retained
body comes from the specialized source at that index. The terminator
law maps every live jump back to its exact original target and
preserves the tested and returned ports.

The compact header has entry and backedge occurrences. `originalOccurrence`
maps the backedge to the selected original feedback occurrence.
`predecessor_bank` preserves the entire typed register bank delivered by
either retained predecessor. `feedback_arrival` identifies that bank on
every continuing arrival covered by the original entry facts.
[Remapping and header laws](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/SCCP/Dispatch/DeleteRoute/Thms.lean)

`runFrom_retained` proves exact runner agreement with the checked
five-block source at any retained index and bank. The composed
`rewrite_runFrom_eq` compares the original and four-block sources from
entry for each concrete bank covered by `Diamond.SCCP.TupleCovers`.
They return or exhaust at the same block budget because every visited
block is retained, including the dispatcher. The proof also gives
`rewrite_returns_iff` without a termination hypothesis.

## Run the example

```lean
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Example

#eval layout (.constant ⟨false⟩)  -- some ([0, 1, 2, 4], some 3)
#eval layout (.constant ⟨true⟩)   -- some ([0, 1, 2, 3], some 3)
#eval layout .overdefined        -- none
#eval compactReturn false 4      -- some none
#eval compactReturn false 5      -- some (some 7)
#eval compactReturn true 5       -- some (some 99)
#eval compactLoop 12             -- some none
```

The layout shows the original block indices in compact order and the
new dispatcher target. The outer option in a run reports admission.
The inner option records native return or exhaustion. The continuing
fixture is the same nonreturning loop checked by the dispatcher rewrite.
[Regressions](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/SCCP/Dispatch/DeleteRoute/Regression.lean)

Rice §3.6, Figure 3.7 (printed p. 26), gives cyclic reachability.
This cleanup uses the existing singleton certificate to remove one
feedback block in the fixed pure quad source. General CFG SCCP, sparse
scheduling, and lowering the compact source into other IRs are outside
this slice.
[Rice dissertation](https://hdl.handle.net/1911/16807) ·
[Wegman–Zadeck](https://doi.org/10.1145/103135.103136)
