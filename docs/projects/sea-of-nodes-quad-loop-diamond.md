# A checked quad loop with an internal diamond

`Quads.Loop.Tail.Diamond.check` reads the original typed quad source
table. It follows two nonempty linear arms from the header test to
the common merge. The merge jumps to the latch, whose true occurrence
returns to the header and whose false occurrence returns a typed
register. The finite-chain checker finds the two routes. Their
segments end immediately before the merge, which is the last jump
block before the latch. The checker requires all source block IDs to
be distinct across entry, header, arms, merge, and latch and to cover
the table. The merge columns stay in true/false order. Each names the
last original block on its arm, while the header targets the first.
[Checker and lowering](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Diamond/Defs.lean)

The source follows Cliff Click's *From Quads to Graphs*, §2 and
Figure 1 for ordered CFG blocks, §3.1 and Figure 6 for current
definitions and pending loop-head inputs, §4.1 and Figure 9 for
associating data with the chosen predecessor, and §6 and Figure 15
for the Region and If graph representation. The pinned manuscript
is Rice TR CRPC-TR93366-S, October 18, 1993, SHA-256
`8b13190b36a8aae0b7b1e622337d99263662487e18144d8e1b379dcea580548b`.
[1993 manuscript](https://web.archive.org/web/20250330055404id_/https://softlib.rice.edu/pub/CRPC-TRs/reports/CRPC-TR93366-S.pdf)

The existing quad join compiler emits each arm into its own numbered
γ child. The child's results are calculated from that arm's local
reaching versions. The selected γ result supplies the complete typed
bank of merge arguments to the shared merge quads and then the latch.
A preheader prefix initializes the θ binder. A continuing latch passes
the whole updated bank back to that binder in one operation. A stopping
latch exposes the result register from the same updated bank.
The target is existing numbered `RVSDG.NestedTheta.Graph`, with γ inside θ.
[Quad join compiler](../../Silmaril/SSA/SeaOfNodes/Quads/Join/Finite/Thms.lean) ·
[Native graph](../../Silmaril/SSA/RVSDG/NestedTheta/Defs.lean)

`Program.selected_predecessor` identifies the source ID selected by the
γ tag. `Program.merge_run` proves that the selected occurrence supplies
the entire bank. `Program.activation_run` gives the latch's exact
continuation tag and bank. `Program.lower_run` charges one entry visit and, for each traversed
arm, the arm's length plus three visits for the header, merge, and latch.
The trace stops at return or the native activation bound. For a
returning native trace, `Program.run_at` proves that the sum is the
minimum source fuel, with exhaustion below it. `Program.source_bounded_iff`
characterizes every successful bounded source run by a native return
whose exact visit count fits the budget. `Program.returns_iff` gives
bidirectional finite returns for the original source table.
[Proof interface](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Diamond/Thms.lean)

The regression enters at block 4, runs true arm 5, feeds back through
latch 1, and then runs false arm 0. The arms supply different numbered
definitions of `y`. The first merged value gives `x = 7` in the
feedback bank. The false arm reads that bank and the next merge gives
`x = 14`. Nine source visits or two θ activations return `14`.
Eight visits or one θ activation exhaust. A counter-one input returns
`12` through the false arm without feedback. The checker rejects
different arm merge targets and a wrong feedback target.
The unequal-arm fixture alternates true, false, true. The arms have
block IDs `[5, 6]` and `[0]`, so the merge predecessor trace is
`[6, 0, 6]`. The longer arm's second block reads and redefines the
first block's value of `y`. The activation costs are `[5, 4, 5]`,
giving a return of `22` at exactly fifteen source visits or three
θ activations. Fourteen visits exhaust. A self-loop on arm block 5
is rejected. The admitted profile is one pure diamond with linear
arms, one merge, one tail test, and a full carried bank.
[Equal-arm regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/Diamond/Regression.lean) ·
[Unequal-arm regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/Diamond/UnequalRegression.lean)

```sh
lake build --wfail +Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.UnequalRegression
make check CHECK_TARGETS='+Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.UnequalRegression +Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Quads.Join.Finite.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Chain.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Thms
```

[Run the unequal-arm profile in typed MLIR CF](sea-of-nodes-quad-diamond-mlir-cf.md).
