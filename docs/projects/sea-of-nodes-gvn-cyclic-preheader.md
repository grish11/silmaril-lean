# Seed cyclic GVN from interned preheader values

`Builder.Preheader.optimize?` accepts a native `Loop.Graph` in the
wrapping i64 producer profile. A word Φ may read a computed preheader
wire on entry. The adapter numbers the actual preheader once, reads IDs
at the exact typed entry operands, and selects the first carried lane
with the same ID as the capture position. Predicates use their own
capture positions. The temporary input bank contains the concrete
original latch tuple followed by the original inputs.
[Adapter](../../Silmaril/SSA/SeaOfNodes/GVN/Cyclic/Builder/Preheader/Defs.lean) ·
[Intern evaluator](../../Silmaril/SSA/SeaOfNodes/GVN/WordNumber/Intern/Thms.lean)

`equal_lane_ids` proves that two word IDs in that one preheader table
denote equal initial latch values for every typed input.
`canonical_word_iff` identifies exactly which lanes select the same
capture position. These positions become the fixed entry operands of
the existing builder. The existing refinement assigns its own
classes to Φ and header vertices. It still compares the entry
position and the relabeled feedback operand in occurrence order.
`normalized_phi_occurrences` exposes both required equalities for
same-class Φ vertices.
[Theorems](../../Silmaril/SSA/SeaOfNodes/GVN/Cyclic/Builder/Preheader/Thms.lean) ·
[Existing builder](sea-of-nodes-gvn-cyclic-builder.md)

## Native rewrite

The prepared loop sends the original guard, exit, and complete feedback
packet through the existing typed pure-table routing. `prepare_initial`
and `prepare_packet` prove equality with the original reads, and
`initial_agrees` initializes the existing cyclic latch invariant on
the original entry tuple. The adapter runs the existing builder and
one-step pass on the prepared graph. It then checks every surviving
header operand and every observation for use of a temporary capture
before restoring the original input interface.

`proposal_restores` proves that restoration succeeds on every checked
deletion in `Pass.proposals` for a view of the prepared loop. Preparation
introduces capture arguments only in the entry column. The prepared
header and its observations read the lifted original arguments or
producer outputs. A proposed redirect reads an available prefix output.
Deletion preserves argument references and only reindexes producer
outputs. Thus every surviving operand and every guard, feedback and
exit wire passes the existing restoration check.

`optimize_eq_scan` equates the current implementation to applying
`restore? loop` inside `Pass.proposals`' ordered `findSome?`. Both select
the first checked deletion, with direct deletions before redirects.
Once the builder succeeds, `optimize_none_iff` says that `none` excludes
every deletion the enumerated proposals can produce at the computed
partition. This says nothing about edits outside those proposals.
`restore?` still checks arbitrary supplied edited graphs for capture
reads.
[Restoration theorems](../../Silmaril/SSA/SeaOfNodes/GVN/Cyclic/Builder/Preheader/Thms.lean)

A successful result keeps the original preheader and entry column and
removes exactly one header binding. `optimize_activation` preserves
the selected transition, including the full simultaneous feedback
tuple, under the existing latch invariant. `optimize_evalBackedges`
preserves every budget, and `optimize_returns` preserves and reflects
finite returns from the original entry. This scope uses one pure
preheader and one shrinking step in the existing loop profile.
[Existing search and deletion](sea-of-nodes-gvn-cyclic-pass.md)

The regression starts two word Φs from separate preheader adds.
They share an ID and initialize the same class. Changing one child or
one feedback operand separates the lanes and blocks this deletion.
On the accepted case the restored loop shrinks from four header
bindings to three, sends `(false, 16, 16)` on the first backedge,
and returns 34 with one backedge of budget. The runnable `proposalScan`
regression enumerates 16 proposals. With matching feedback, both of the
two checked deletions restore. With mismatched feedback, the loop still
builds and the same 16 proposals yield zero checked deletions. The
universal restoration theorem rules out a first rejected restoration
followed by a later successful one in this scan.
[Native regression](../../Silmaril/Proofs/SSA/SeaOfNodes/GVN/Cyclic/Builder/Preheader/Regression.lean)

```sh
topic=SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader
make check CHECK_TARGETS="+Silmaril.$topic.Thms +Silmaril.Proofs.$topic.Regression +Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Deletion.Regression"
lake env leanchecker "Silmaril.$topic.Thms"
lake env leanchecker "Silmaril.Proofs.$topic.Regression"
```

Click's PLDI ’95 §3.1 step 3 supplies the opcode-and-numbered-input
lookup for acyclic preheader values. The cyclic builder still follows
the dissertation's ordered use-def edges in §§4.1–4.2. The adapter
connects these two steps at the native entry Φ operands.
[Pinned PLDI ’95 PDF](sea-of-nodes/optimization/sea-of-nodes-gvn-pass.md) ·
[Rice dissertation](https://hdl.handle.net/1911/16807)
