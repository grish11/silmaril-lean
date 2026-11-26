# Repeat preheader-seeded cyclic GVN on a native loop

`Iteration.Preheader.normalize` runs the existing
`Builder.Preheader.optimize?` on the current native wrapping-word loop.
A successful call restores the original input interface before the next
attempt. Each subsequent call prepares the current header, builds a fresh
view, recomputes the stable classes, and checks the next rewrite and its
restoration. The driver shares the existing cyclic iteration's result type
and one-binding fuel accounting. `Iteration.run_eq_runWith` connects the
direct-entry API to the same step-parameterized driver.
[Driver](../../Silmaril/SSA/SeaOfNodes/GVN/Cyclic/Iteration/Preheader/Defs.lean) ·
[Checked preheader step](sea-of-nodes-gvn-cyclic-preheader.md)

`run_entry` preserves the preheader and full entry Φ packet at every
fuel prefix. The input, carried, entry and result signatures are fixed by
the driver type. `run_progress` proves that the final header length plus
the number of deletions equals the original length and that each
successful step spends one unit of fuel. The initial binding count
suffices because a loop with an empty header cannot accept a further
shrinking step. `normalize_evalBackedges` preserves the original
evaluator result for every typed input and backedge budget, including
budget exhaustion. `normalize_returns` preserves and reflects finite
returns.
[Driver theorems](../../Silmaril/SSA/SeaOfNodes/GVN/Cyclic/Iteration/Preheader/Thms.lean)

`normalize_stopped` says that a fresh call to
`Builder.Preheader.optimize?` on the returned native graph returns
`none`. `normalize_saturated` also supplies the actual builder result
on the final prepared graph and rules out all accepted proposals in
that view's enumeration at its computed stable partition.
`Builder.Preheader.prepare_builds` applies at the original header and
at every restored header, so the terminal result needs no separate
build assumption. The guarantee covers the implemented single-delete and
single-redirect-then-delete proposals.
[Restoration and proposal scope](sea-of-nodes-gvn-cyclic-preheader.md#native-rewrite)

## Native regression

Three separate preheader adds feed the entry Φ lanes. Matching
feedback gives equal classes for the three independently computed
header increments. The first accepted rewrite shrinks the header from
five bindings to four. Rebuilding on that restored graph admits a second
rewrite to three bindings. The regression checks that the builder
succeeds on both restored headers and applies the saturation theorem
to the final header. The restored loop sends the complete packet
`(false, 30, 30, 30)` on the first backedge and returns 99 with one
backedge of budget. In a second case, distinct feedback sources keep
the increments separate. The prepared graph builds and the native
checker stops with zero deletions.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/GVN/Cyclic/Iteration/Preheader/Regression.lean)

```sh
topic=SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader
make check CHECK_TARGETS="+Silmaril.$topic.Thms +Silmaril.Proofs.$topic.Regression +Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Deletion.Regression"
lake env leanchecker "Silmaril.$topic.Thms"
lake env leanchecker "Silmaril.Proofs.$topic.Regression"
```

Click PLDI ’95 §3.1 step 3 motivates value numbering and removal of
redundant computations. This driver composes the checked preheader
numbering and the existing cyclic refinement and deletion, whose
ordered use-def correspondence follows the Rice dissertation §§4.1–4.2.
The admission proof concerns typed origin lookup and producer order in
this representation. Saturation covers this implementation's current
proposal list.
[Pinned PLDI ’95 PDF](sea-of-nodes/optimization/sea-of-nodes-gvn-pass.md) ·
[Rice dissertation](https://hdl.handle.net/1911/16807)
