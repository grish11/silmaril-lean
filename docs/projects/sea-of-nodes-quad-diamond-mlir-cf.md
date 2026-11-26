# A checked unequal-arm quad loop in typed MLIR CF

The input is the checked [quad diamond loop](sea-of-nodes-quad-loop-diamond.md)
from #3547. Cliff Click's *From Quads to Graphs*, Rice TR CRPC-TR93366-S
(October 18, 1993), gives the source setting in §2 and Figure 1 (ordered
quad blocks), §3.1 and Figure 6 (current definitions and pending header
inputs), and §4.1 and Figure 9 (associating an input with its predecessor).
The manuscript SHA-256 is
`8b13190b36a8aae0b7b1e622337d99263662487e18144d8e1b379dcea580548b`.
[1993 manuscript](https://web.archive.org/web/20250330055404id_/https://softlib.rice.edu/pub/CRPC-TRs/reports/CRPC-TR93366-S.pdf)

The checker admits an entry, one header split, two nonempty disjoint
linear arms of potentially different lengths, one common merge, and
one latch. The latch's true occurrence feeds back to the header and
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
header quads. `predecessor_frame` identifies the original last block of
either arm and the entire bank it passes into the merge. `arm_run` covers
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
