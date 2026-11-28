# A checked unequal-arm quad loop in typed MLIR CF

The input is the checked [quad diamond loop](sea-of-nodes-quad-loop-diamond.md)
from #3547. Cliff Click's *From Quads to Graphs*, Rice TR CRPC-TR93366-S
(October 18, 1993), gives the source setting in §2 and Figure 1 (ordered
quad blocks), §3.1 and Figure 6 (current definitions and pending header
inputs), and §4.1 and Figure 9 (associating an input with its predecessor).
The manuscript SHA-256 is
`8b13190b36a8aae0b7b1e622337d99263662487e18144d8e1b379dcea580548b`.
[1993 manuscript](https://web.archive.org/web/20250330055404id_/https://softlib.rice.edu/pub/CRPC-TRs/reports/CRPC-TR93366-S.pdf)

The checker admits an entry, one header split, two disjoint linear
arms of potentially different lengths, one common merge, and one
latch. One arm may go directly from the header to the merge. The latch's true occurrence feeds back to the header and
its false occurrence returns a register. The emitter keeps the original
IDs, emits typed `cf.br` and `cf.cond_br`, and passes a full bank as
block arguments. Each edge resolves its operands from the predecessor's
compiled reaching-version map. The native loop scalar emitter supplies
the word and comparison operations. Registers can mix fixed-width
words and predicates encoded as `i1`. The separate CF return label costs
one visit because the latch's `cf.cond_br` has two successor edges.
The source entry is the external CF entry. No checked edge can reach
its labeled copy in the block table.
[Emitter](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Diamond/MLIR/CF/Defs.lean)

`split_frame` identifies the actual taken target after evaluating the
header quads. `predecessor_frame` gives the bank sent by the last block
of a nonempty arm or by the header when the test selects a direct
edge. `arm_run` covers
the intervening visits and `latch_frame` identifies both feedback and
exit packets. For every source budget `n`, `lower_run` equates the
original source run and the typed CF run at `n + 1`, including exhausted
runs. `native_run` connects the existing numbered γ/θ graph at its
activation budget by adding one to the sum of source visits. This
entry point carries the full bank.
[Proof interface](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Diamond/MLIR/CF/Thms.lean)

Build the fixture with
`lake build --wfail +Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Example.Defs`.
Paste the following into `QuadDiamondCF.lean` and run
`lake env lean -DwarningAsError=true QuadDiamondCF.lean` from the repository root.

```lean
module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Example

#eval predecessors 3    -- [6, 0, 6]
#eval runSource 15      -- some 22
#eval runCF 16          -- some 22
#eval runCF 15          -- none
```

The trace visits arms `[5, 6]`, `[0]`, and `[5, 6]` with two
feedback edges. The branch predicate is overwritten after feedback.
The regression checks the actual emitted CF edges and their argument
banks independently of the displayed source trace.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/Diamond/MLIR/CF/Regression.lean)

## Prune the carried header arguments

`CF.Pruned.lower` consumes the same
[checked projection](sea-of-nodes-quad-diamond-phi-pruning.md) as the
numbered RVSDG emitter. Entry and latch feedback project their outgoing
version maps in register order. The header uses the checked renamed
producer table to reconstruct the entire post-header bank. The two
arms, common merge and latch keep their original block IDs and full
argument banks. The checker retains any field needed to reconstruct
that bank, including fields used later in an arm or by the latch.
[Pruned emitter](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Diamond/MLIR/CF/Pruned/Defs.lean)

`entry_frame` and `latch_frame` identify the actual projected frames,
and `site_frame` gives exact successor routing and arguments at every
original block. `lower_run` preserves return and exhaustion at source
fuel `n` and CF fuel `n + 1`. `run_agrees` compares both CF emitters at
any common fuel. The scope is the same checked pure diamond and one
tested latch. The projection shrinks only the carried header bank.
[Proof interface](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Diamond/MLIR/CF/Pruned/Thms.lean)

Build with
`lake build --wfail +Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Example.Defs`.
Paste the block into `PrunedQuadDiamondCF.lean` and run
`lake env lean -DwarningAsError=true PrunedQuadDiamondCF.lean`.

```lean
module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF

#eval Pruned.Example.headerArities                       -- (some 7, some 6)
#eval Example.predecessors 3                             -- [6, 0, 6]
#eval Example.runSource 15                               -- some 22
#eval Pruned.Example.runCF 16                            -- some 22
#eval Pruned.Example.runCF 15                            -- none
#eval (Pruned.Example.rejects Example.stride.index,
  Pruned.Example.rejects Example.count.index)            -- (true, true)
```

The removed header argument is the old predicate, which the header
overwrites. The stride reaches the longer arm and the counter reaches
the latch, so proposing to drop either one fails the existing check.
The regression checks both incoming merge packets and both projected
feedback frames in the emitted CFG.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/Diamond/MLIR/CF/Pruned/Regression.lean)

## Compare the two pruned targets

Import
`Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Comparison.Thms`
for the public comparison API. Both lowerings consume the same checked
projection. The numbered RVSDG graph receives the typed source bank,
and the CF graph receives its existing `encodeValues` representation.
`Comparison.denotePart_eq` equates the existing partial observations
by encoding the RVSDG singleton result as a returned CF environment.
`Comparison.returns_iff` transfers finite return witnesses at the
targets' own budgets. `Comparison.diverges_iff` covers absence of a
return at every finite budget.
[Public theorems](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Diamond/MLIR/CF/Pruned/Comparison/Thms.lean)

`Comparison.run_at_source_visits` supplies a concrete CF budget for a
numbered RVSDG activation bound. It charges one source visit per original
block on the selected trace, then the CF return visit. The fixture uses
the original merge predecessors `[6, 0, 6]`, with two feedback edges.
Three numbered θ activations and sixteen CF visits return the same word.
[Checked RVSDG trace](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Diamond/Prune/Thms.lean) ·
[CF route and feedback](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Diamond/MLIR/CF/Pruned/Thms.lean)

Use the same fixture build command above. Paste this block into
`ComparePrunedQuadDiamond.lean` and run
`lake env lean -DwarningAsError=true ComparePrunedQuadDiamond.lean`.

```lean
module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF

#eval Example.predecessors 3                                    -- [6, 0, 6]
#eval (Pruned.Example.runRVSDG 3, Pruned.Example.runCF 16)        -- (some 22, some 22)
#eval (Pruned.Example.runRVSDG 2, Pruned.Example.runCF 15)        -- (none, none)
```

The last line shows exhaustion at those two bounds. The regression also
checks the partial observation `Part.some` of the encoded return.
[Comparison regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/Diamond/MLIR/CF/Pruned/Comparison/Regression.lean)

## Check an equation between two pruned loops

Import
`Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Comparison.Equation.Thms`.
`Equation.nativeEquation` and `Equation.prunedEquation` package the
actual numbered γ/θ graphs in the existing nested RVSDG runtime-observation
sentence. This sentence fits the inner diamond. The native pure-loop
institution's equation container uses a linear header producer table.
The unpruned graph's finite returns are exactly the quad source runner's
finite returns.
[Nested runtime sentences](../../Silmaril/SSA/RVSDG/NestedTheta/Institution/RuntimeObservation/Defs.lean) ·
[Native pure-loop equations](../../Silmaril/SSA/SeaOfNodes/Loop/Institution/Defs.lean) ·
[Quad adequacy](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Diamond/Thms.lean)

`Equation.rvsdg_satisfaction` compares the two sentences in the concrete
word model. Independently, `Equation.cf_satisfaction` relates native
satisfaction to equality of the two emitted CF observations at every
typed CF valuation. The proof uses `encodeValues` for the shared ordered
entry bank, including its `i1` predicates, and the exact singleton word
return from the comparison theorem. `Equation.cf_at_iff` gives the same
equivalence at one native valuation. Both sides must share the typed
entry bank and result width. Their checked block tables and masks may
differ.
[Equation API](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Diamond/MLIR/CF/Pruned/Comparison/Equation/Thms.lean)

The second program adds the carried stride in short arm block 0, first
selected after feedback. Both follow merge predecessors `[6, 0, 6]`
and feed back the same first bank. The two final words, 22 and 24, refute
the equation at this valuation. The smaller budgets below give bounded
exhaustion. The equation uses partial observations, where absence requires
failure to return at every finite budget.
[Inequation regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/Diamond/MLIR/CF/Pruned/Comparison/Equation/Regression.lean)

Build with
`lake build --wfail +Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Comparison.Equation.Example.Defs`.
Paste the block into `QuadDiamondEquation.lean` and run
`lake env lean -DwarningAsError=true QuadDiamondEquation.lean`.

```lean
module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Comparison.Equation.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Comparison.Equation.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Equation.Example

#eval rvsdgResults 3   -- (some 22, some 24)
#eval cfResults 16     -- (some 22, some 24)
#eval rvsdgResults 2   -- (none, none)
#eval cfResults 15     -- (none, none)
```

## Permute the typed entry interface

Import `Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex.Thms`.
An `EntryPermutation` maps each original entry port to a new port of
the same sort, with a typed inverse. `pull` reads the new valuation in
original register order. The CF emitter uses this map to bind the
preheader's external names. The numbered RVSDG construction changes the
outer argument wires and retains the original θ body. The original
local register definitions, labels, predecessor occurrences and checked
carried mask supply both lowerings.
[Typed entry API](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Diamond/MLIR/CF/Pruned/Reindex/Defs.lean)

`graph_run` and `cf_run` preserve each target's own budget at
corresponding valuations. `graph_observe` and `cf_observe` give the same
law for partial observations. `native_satisfaction`,
`rvsdg_satisfaction` and `cf_satisfaction` reflect and preserve the
native equation across the entire permuted entry interface. CF quantifies
over all typed environments, using the existing encoding of words and
`i1` predicates. The scope is the checked pure unequal-arm profile, with
a common word result for equations.
[Proof interface](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Diamond/MLIR/CF/Pruned/Reindex/Thms.lean)

The fixture moves a true predicate before the last two words and
exchanges the result and stride word positions. The correctly paired
input takes merge predecessors `[6, 0, 6]` and returns 22 after two
feedback edges. Supplying those two words in the wrong order still
typechecks and returns 34 on both emitted targets.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/Diamond/MLIR/CF/Pruned/Reindex/Regression.lean)

Build with
`lake build --wfail +Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex.Example.Defs`.
Paste into `QuadDiamondEntry.lean` and run
`lake env lean -DwarningAsError=true QuadDiamondEntry.lean`.

```lean
module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex.Example

#eval predicateBit                   -- 1
#eval predecessors                   -- [6, 0, 6]
#eval results paired 3 16            -- (some 22, some 22)
#eval results wrongPairing 3 16      -- (some 34, some 34)
```

### Compose entry permutations

Import `Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex.Composition.Thms`.
`first.trans second` sends each original port through `first` and then
`second`. Its valuation is `pull first (pull second input)`. The
`cfNames_trans` and `wires_trans` laws give equality of the external
bindings before execution. `lowerCF_trans` and `graph_trans` lift the
equalities to the actual emitted CFG and numbered graph. Both views use
the checked mask, local labels and predecessor occurrences. The
`lowerCF_refl` and `graph_refl` laws recover the original targets under
the identity permutation.
[Composition API](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Diamond/MLIR/CF/Pruned/Reindex/Composition/Thms.lean)

The fixture moves the predicate and then applies two overlapping word
swaps. The composed and successive emissions return 22 at three
numbered θ activations and sixteen CF visits, with merge predecessors
`[6, 0, 6]`. Reversing the swaps at the same typed valuation gives 86
under the eight-bit arithmetic model.
[Composition regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/Diamond/MLIR/CF/Pruned/Reindex/Composition/Regression.lean)

Build with
`lake build --wfail +Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex.Composition.Example.Defs`.
Paste into `ComposeQuadEntry.lean` and run
`lake env lean -DwarningAsError=true ComposeQuadEntry.lean`.

```lean
module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex.Composition.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex.Composition.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex.Composition.Example

#eval predicateBit                 -- 1
#eval predecessors                 -- [6, 0, 6]
#eval sequentialResults            -- (some 22, some 22)
#eval results (first.trans second) -- (some 22, some 22)
#eval results reversed             -- (some 86, some 86)
```

### Transport a partial equation through both permutations

Import
`Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex.Composition.Equation.Thms`.
`rvsdg_at_trans_iff` and `cf_at_trans_iff` compare two actual emitted
programs at a final valuation. The corresponding native valuation is
`pull first (pull second input)`. The `rvsdg_satisfaction_trans` and
`cf_satisfaction_trans` laws lift this comparison to the existing
native equation over all valuations. The CF law covers every typed
environment of the final entry interface.
[Public equation API](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Diamond/MLIR/CF/Pruned/Reindex/Composition/Equation/Thms.lean)

The observations are partial values. Their equality includes the case
where both sides have no finite return, and a finite return on only one
side refutes the equation. To carry an original valuation forward, use
`pull (first.trans second).symm` to supply the matching final input
and `pull_roundtrip` to recover the original bank. The
`graph_roundtrip` and `lowerCF_roundtrip` laws recover the original
emitted graph and CFG by applying the inverse. These laws use the same
checked pure unequal-arm profile, masks, and predecessor order.
[Composition and inverse laws](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Diamond/MLIR/CF/Pruned/Reindex/Composition/Thms.lean)

The runnable fixture reuses the short-arm inequation and the two mixed
entry permutations above. The two programs take predecessors
`[6, 0, 6]` with two feedback edges. At the paired valuation the base
program returns 22 and the variant returns 24 in both targets. The
Lean regression checks inequality of their partial observations at that
valuation.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/Diamond/MLIR/CF/Pruned/Reindex/Composition/Equation/Regression.lean)

Build with
`lake build --wfail +Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex.Composition.Equation.Example.Defs`.
Paste into `TransportQuadEquation.lean` and run
`lake env lean -DwarningAsError=true TransportQuadEquation.lean`.

```lean
module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex.Composition.Equation.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex.Composition.Equation.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex.Composition.Equation.Example

#eval results.1  -- (some 22, some 22)
#eval results.2  -- (some 24, some 24)
```


## Take a direct edge to the merge

The conditional assignment in *From Quads to Graphs* §3, Figure 4,
has a bypass occurrence into the merge. Its Φ takes the current
definition on that occurrence. In the checked profile a direct arm
has zero intervening visits. The header is its original predecessor
and supplies the post-header bank to the merge. In numbered RVSDG
the corresponding γ child forwards its input wires. In typed CF the
header branches directly to the original merge with the same values.
The common merge still jumps to the distinct tested latch. At least
one arm has a block, and a cycle inside an arm fails the source check.
[1993 manuscript](https://web.archive.org/web/20250330055404id_/https://softlib.rice.edu/pub/CRPC-TRs/reports/CRPC-TR93366-S.pdf)

For a checked projection, `Pruned.lower_run` relates the source and
CF at budgets `n` and `n + 1`. The projected RVSDG
`Checked.returns_iff` gives finite-return correspondence at the same
typed input. `Comparison.source_diverges_iff` and
`Comparison.diverges_iff` transfer absence of a return at **every**
finite budget through both emitted graphs.
[Projected RVSDG theorems](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Diamond/Prune/Thms.lean) ·
[Comparison theorems](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Diamond/MLIR/CF/Pruned/Comparison/Thms.lean)

Build with
`lake build --wfail +Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Example.Bypass`.
Paste the block into `PrunedQuadBypass.lean` and run
`lake env lean -DwarningAsError=true PrunedQuadBypass.lean`.

```lean
module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Example.Bypass
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Example.Bypass

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Example.Bypass

#eval predecessors 3                              -- [0, 2, 0]
#eval (runSource 14, runCF 15, runRVSDG 3)          -- (some 19, some 19, some 19)
#eval (runSource 13, runCF 14, runRVSDG 2)          -- (none, none, none)
```

The second activation takes the bypass after feedback. Its CF edge
from header 2 to merge 3 passes the newly written result 13. The
fixture takes two feedback edges and removes one of seven carried
header arguments.
[Bypass regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/Diamond/MLIR/CF/Pruned/BypassRegression.lean)
