# Conditional constant propagation with two feedback occurrences

The existing pure `Loop.Graph` has one feedback occurrence. The checked
quad tail diamond has two incoming occurrences at its internal merge, followed
by a single tested latch. `Quads.Loop.Tail.TwoBackedges.Program` adds a
fixed five-block pure quad shape where both feedback blocks jump separately
to the loop header. It uses `Tail.Source.runFrom` for native execution.
[One-backedge analysis](rice-loop-sccp.md) ·
[Checked quad diamond](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Diamond/Defs.lean) ·
[Two-backedge source](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/Defs.lean)

Block 0 initializes the bank and jumps to header 1. The header runs its
assignments and either returns or jumps to dispatch block 2. The dispatch
test selects block 3 on true or block 4 on false. Each executes its own
ordered assignments and passes its entire resulting bank to header 1.
The analysis tracks four marks for entry, true feedback, false feedback
and exit. Both abstract feedback columns read the same post-header bank.

`SCCP.transfer` compiles the quad blocks through the existing typed version
map and uses the shared abstract producer evaluator. `phiFacts_le_iff`
characterizes the join of the marked columns. The transfer is monotone in
the optimistic-bottom order, the dual of Rice's optimistic top. The
existing finite-height iterator computes its least fixed point with rank
bound `4 + 2n + 2` for `n` carried fields. Analysis rounds and native block
fuel are independent. [Equations](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/SCCP/Defs.lean) ·
[Theorems](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/SCCP/Thms.lean)

`Program.source_header` connects a labeled activation to the native source
runner. `SCCP.solve_arrives` marks the exact incoming occurrence of every
finite header arrival and covers its complete latch, including prefixes
that never return. `SCCP.solve_source_return` covers any actual return from
block 0 at any native budget. A constant result fact therefore gives
equality on covered returns.
[Native step law](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/Thms.lean)

## Run the example

```lean
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Example

#eval feedbackBytes                -- (constant 99, constant 7)
#eval report (.constant ⟨false⟩)   -- (true, false, true, true, constant 7, constant 7)
#eval report .overdefined          -- (true, true, true, true, overdefined, overdefined)
#eval firstFeedback false          -- some (false, 7)
#eval firstFeedback true           -- some (true, 99)
#eval nativeReturn false 4         -- none
#eval nativeReturn false 5         -- some 7
#eval nativeReturn true 5          -- some 99
```

The known dispatch selects the false feedback column, so the byte `99`
from the true column never enters the join. When the dispatch fact is
overdefined, both feedback occurrences are marked and the byte widens.
The checks also instantiate return soundness to show that every native
return for the known-false input equals `7`.
[Checked regressions](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/SCCP/Regression.lean)

Rice §3.6 Figure 3.7 (printed p. 26) supplies cyclic reachability, and
§3.7 Figure 3.8 (p. 28) supplies the conditional gates for constant facts.
Wegman and Zadeck's *Constant Propagation with Conditional Branches*
supplies the executable-edge baseline. This slice adds a second separately
marked feedback column to one pure header. Arbitrary CFGs, sparse scheduling
for this shape, and rewrites remain separate coverage obligations.
[Repository source inventory](sea-of-nodes/coverage.md#rice-dissertation) ·
[Rice dissertation](https://hdl.handle.net/1911/16807) ·
[Wegman–Zadeck](https://doi.org/10.1145/103135.103136)
