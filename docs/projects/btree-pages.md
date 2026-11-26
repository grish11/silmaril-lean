# Routed B-tree lookup on numbered pages

Import `Silmaril.Semantics.BTreePages.Thms` for the definitions and public
theorems. The implementation uses the [abstract leaf-oriented B-tree](abstract-btree.md)
and the [numbered-page calculus](page-completion.md). The integration was checked
with the exact dependency commits [`d064372d49d5e8920ad433f698835a0e90df812d` (PR #3520)](https://github.com/hiloopai/silmaril-lean/commit/d064372d49d5e8920ad433f698835a0e90df812d)
and [`27c300bfd81aae4c8c3d01ba89d5b6ae957fd29e` (PR #3534)](https://github.com/hiloopai/silmaril-lean/commit/27c300bfd81aae4c8c3d01ba89d5b6ae957fd29e).

## Representation

`Position` is a path of zero-based child slots, with `[]` at the root. A `Layout Id`
assigns a stable page ID to each position. Only paths that reach nodes through
`atPath` contribute to `Footprint`, which is defined entirely from the abstract
tree and layout. A leaf page carries its ordered bindings. A branch page carries
inclusive upper dividers, the IDs of their children, and the rightmost child ID.
[`Defs.lean`](../../Silmaril/Semantics/BTreePages/Defs.lean)

`WellFormed` combines abstract `Tree.Valid` with injectivity of the layout on
reachable positions. This excludes both cycles and sharing between positions of
one represented tree, even when two positions encode the same payload. IDs for
unreachable positions are unrestricted. `Represents store layout tree` is a set
of ordinary memories. The slot at each reachable ID must be `.defined` with the
payload computed by `pageAt`. Other slots may be absent, UNDEF, or defined.
`represents_over` constructs a witness in the function-backed `Page.mapStore`
over any supplied outside slots. Operational theorems apply to any `Page.Model`
with a representative. [`Thms.lean`](../../Silmaril/Semantics/BTreePages/Thms.lean)

## Lookup and framing

Run `lookup key tree.height (layout [])` as a `Page.Program`. It reads one page
per level. `inspect` decides whether to return a leaf result or descend to a child
ID. `lookupStep` exposes that one-read operation, and `lookupStep_run_iff` provides
its effect-free result contract on a defined slot. `inspect_branch` proves that
the physical pointer belongs to the exact slot selected by abstract
`Branch.route`, including equality at an upper divider and the rightmost case.
A page kind inconsistent with the supplied height reaches `Page.Program.diverge`.
The ordinary calculus reports absent and UNDEF reads as distinct UB outcomes.

For every key and represented tree, `lookup_run_iff` provides existence and
uniqueness of the operational outcome. The program returns normally, with
`tree.lookup? key`, the exact original memory, and an empty edit list. This rules
out UB and divergence and covers `none` on a miss. `lookup_subtree_run_iff`
starts the same program at any reachable subtree. `lookup_orderedMap_run_iff`
also identifies the result with the represented `OrderedMap`.

`represents_congr` transports representation across any two memories that agree
on the footprint. `lookup_frame` gives the same result after arbitrary changes
outside that footprint and returns the resulting memory unchanged.
`lookup_frame_of_disjoint` specializes the rule to changes confined to a second
root's disjoint footprint. `represents_set_outside` preserves a representation
under a point update to any ordinary slot outside its footprint.

`shared_representation_iff` characterizes when two well-formed layouts can share
a function-backed store. They must demand equal payloads at the IDs they share.
Disjoint footprints satisfy this condition automatically. `shared_lookup_preserves`
also handles compatible overlap in a shared store because a lookup preserves all
of memory. Overlap grants shared read access. Mutable ownership, structural or
leaf updates, byte encoding, and engine-specific adapters are outside the proved
scope.

## Verification

Use the pinned Lean toolchain in the repository. `Checks.lean` constructs
ordinary three-read runs for a divider hit, an interior child hit, a rightmost
hit, and a miss. It also covers an unrelated UNDEF slot, an UNDEF read fault,
a disjoint footprint change, and preservation of an overlapping leaf root.
[`Checks.lean`](../../Silmaril/Semantics/BTreePages/Checks.lean)

```sh
lake build --wfail +Silmaril.Semantics.BTreePages.Thms +Silmaril.Semantics.BTreePages.Checks
make check CHECK_TARGETS='+Silmaril.Semantics.BTreePages.Thms +Silmaril.Semantics.BTreePages.Checks'
awk '/^theorem / { print "#print axioms Silmaril.Semantics.BTreePages." $2 }' \
  Silmaril/Semantics/BTreePages/Thms.lean | \
  { printf 'import Silmaril.Semantics.BTreePages.Thms\n'; cat; } | \
  lake env lean -DwarningAsError=true --stdin
```
