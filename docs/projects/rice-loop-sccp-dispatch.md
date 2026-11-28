# Specialize the dispatcher of the two-backedge quad loop

`Dispatch.check model program inputFacts` runs the existing least-solution
analysis for the fixed five-block pure quad profile. It accepts when exactly
one of the two feedback occurrences is marked. The returned `Checked` carries
the admitted side and evidence that the other side is unmarked. The
correctness theorems apply to each concrete entry bank covered by
`Diamond.SCCP.TupleCovers inputFacts entry`.
[Two-backedge analysis](rice-loop-sccp-two-backedges.md) ·
[Checker and source rewrite](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/SCCP/Dispatch/Defs.lean)

`SCCP.solve_dispatch_marked` extends a covered header arrival by one native
feedback step to justify that the selected occurrence is marked. It applies
whenever the header continues, including along an execution that never returns.
`Checked.dispatch_eq` then identifies that occurrence with the checked side.

`Checked.source` replaces block 2's conditional terminator by a direct
jump to the original feedback block. It keeps the five block indices,
all block bodies and both jumps into the header. Since dispatch still
costs one native block visit, `Checked.runFrom_eq` gives agreement at
every common block budget. `Checked.returns_iff` preserves and reflects
finite return values.
[Checked laws](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/SCCP/Dispatch/Thms.lean)

## Run the example

```lean
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.Example

#eval jumpTarget (.constant ⟨false⟩)   -- some 4
#eval jumpTarget (.constant ⟨true⟩)    -- some 3
#eval jumpTarget .overdefined         -- none
#eval rewrittenReturn false 4         -- some none
#eval rewrittenReturn false 5         -- some (some 7)
#eval rewrittenReturn true 5          -- some (some 99)
#eval loopingReturn 12                -- some none
```

The outer option reports whether the checker admitted the rewrite. The
inner option is the result of running the emitted quad source. The
looping fixture takes the selected feedback indefinitely, and the
regression proves that it returns at no budget. An overdefined selector
marks both routes in the returning fixture, so the checker declines it.
[Regressions](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/SCCP/Dispatch/Regression.lean)

Rice §3.6, Figure 3.7 (printed p. 26), derives cyclic reachability, and
§3.7, Figure 3.8, gates transfer by executable control. This slice uses
that reachability evidence to remove a successor of a fixed pure quad
dispatcher. Block deletion, arbitrary CFGs, and sparse scheduling are
outside the rewrite's scope.
[Rice dissertation](https://hdl.handle.net/1911/16807) ·
[Wegman–Zadeck](https://doi.org/10.1145/103135.103136) ·
[Repository inventory](sea-of-nodes/coverage.md#rice-dissertation)
