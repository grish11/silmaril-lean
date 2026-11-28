# Pruning the carried bank of a quad diamond

`Quads.Loop.Tail.Diamond.Prune.prune` derives a mask for the checked
unequal-arm profile. The pass feeds the compiled header's operand rows
and complete outgoing bank to the existing backward liveness sweep.
It retains the return slot for the stop packet. `checkMask` accepts a
strict reduction only if the header producers and every outgoing wire
can be renamed into the smaller input bank.
[Checked profile and source pin](sea-of-nodes-quad-loop-diamond.md) ·
[Reused quad pruning](sea-of-nodes-quad-loop-phi-pruning.md) ·
[Definitions](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Diamond/Prune/Defs.lean)

The check makes every post-header value available, including the split
condition, uses on either arm, and values needed by the merge, latch
test, return, or future feedback. It can retain a field that a later
block overwrites. This is conservative carried Φ selection in the
loop-head and predecessor sense of Cliff Click's *From Quads to
Graphs*, §§3.1 and 4.1.
[1993 manuscript](https://web.archive.org/web/20250330055404id_/https://softlib.rice.edu/pub/CRPC-TRs/reports/CRPC-TR93366-S.pdf)

The numbered graph initializes and feeds back only the retained fields
at its θ vertex. The header reconstitutes the full bank in front of the
existing γ, merge, and latch code. The γ children and their source ID
map keep the original occurrence order. `Checked.header_agrees`
identifies the reconstructed bank, `Checked.trace_agrees` gives the same
selected occurrences at every activation bound, and
`Checked.activation_agrees` proves the actual emitted tag and projected
bank. `Checked.run_agrees` preserves all native budgets and exhaustion.
The source budget and bidirectional finite-return theorems then reuse
the checked unequal-arm correspondence.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Diamond/Prune/Thms.lean)

The shared fixture removes the old predicate, reducing the actual θ
argument count from six to five. The header writes a fresh split
predicate on each activation, and the latch writes its own test. The
checker rejects dropping `x`, which the header reads, or `saved`, which
the longer arm reads. The pruned trace still selects merge predecessors
`[6, 0, 6]` and returns `22` after three θ activations or fifteen source
visits. Fourteen source visits exhaust.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/Diamond/Prune/Regression.lean)

```sh
lake build --wfail +Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Prune.Regression
make check CHECK_TARGETS='+Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Prune.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.UnequalRegression +Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Prune.Thms
```

[Run the checked projection in typed MLIR CF](sea-of-nodes-quad-diamond-mlir-cf.md#prune-the-carried-header-arguments).
