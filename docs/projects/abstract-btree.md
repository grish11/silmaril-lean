# Abstract leaf-oriented B-tree

`Silmaril.Semantics.BTree` models ordered bindings in the leaves of a finite
B+-tree shape. Each interior divider is an inclusive upper fence for its
left child. Routing chooses the first fence greater than or equal to the
query, or the explicit rightmost child. The tree is parameterized by the key
and value types. Validity and lookup use a `LinearOrder` on the keys.
[Definitions](../../Silmaril/Semantics/BTree/Defs.lean) ·
[SQLite file format, B-tree pages](https://sqlite.org/fileformat2.html#b_tree_pages)

## Invariants and operations

- A leaf has an ordered list of bindings. A branch with `n` dividers has
  exactly `n + 1` children, all one level lower. The height index gives all
  leaves the same depth. Valid branches have at least one divider.
- Leaves have strictly increasing keys. The inherited interval is
  `(lower, upper]`, with either endpoint optional. At a branch each divider
  lies strictly between the current endpoints. It supplies the upper bound
  for its left child and the lower bound for the remaining children. The
  rightmost child inherits the upper bound. The root is unbounded.
- A divider may be absent from the leaf bindings, and empty leaves are
  allowed. Minimum leaf occupancy, maximum fanout, prescribed branching
  factors and byte capacity are outside validity. This slice covers point
  lookup and the in-order binding view. It has no insert, delete, split,
  merge, or page allocation operations.
- `Branch.route_get` connects the selected zero-based slot to the child in
  slot order. `Node.entries_ordered` and `Node.entries_inRange` establish
  global key order and inherited bounds. `Node.lookup_eq_entries` equates
  routed lookup to lookup in the flattened leaf bindings. `Tree.toOrderedMap`
  exposes the existing ordered-map view, with hit and miss characterizations
  in `Tree.lookup_eq_some_iff` and `Tree.lookup_eq_none_iff`.
  [Statements](../../Silmaril/Semantics/BTree/Thms.lean)

## Inventory

| Existing abstraction | Role in a refinement |
| --- | --- |
| [OrderedMap](../../Silmaril/Semantics/OrderedMap/Thms.lean) | Reused as the contents specification and for binding membership. |
| [Prolly](../../Silmaril/Semantics/Prolly/Defs.lean) and [Prolly routing](../../Silmaril/Semantics/Prolly/Routing/Thms.lean) | Already model height-indexed leaf data and first-inclusive-fence routing. Every child there carries its actual maximum key and shape is built by a chunking policy. Arbitrary upper fences and an unfenced rightmost child need the branch shape here. |
| [SQLite `ReadModel`](../../Silmaril/Formats/Sqlite/BTree/Query/ReadModel/Defs.lean) | The existing row-list and equality lookup interface for SQL consumers. A later adapter can instantiate it using the abstract bindings and lookup. |
| [SQLite file image](../../Silmaril/Formats/Sqlite/File/Defs.lean), [table leaf](../../Silmaril/Formats/Sqlite/TableLeaf/Defs.lean), [leaf writer](../../Silmaril/Formats/Sqlite/BTree/LeafWrite/Thms.lean), and [multi-divider interior](../../Silmaril/Machine/SqliteVfs/FileView/Admission/InteriorChild/MultiDivider/Thms.lean) | Byte-view bounds, packed page decoding, restricted leaf writes, and a restricted interior selection and fill contract. The interior profile uses 512-byte pages without reserved space. The available decoders cover particular physical layouts. |
| [SQLite VFS page fill](../../Silmaril/Machine/SqliteVfs/PageRead/Thms.lean), [file-view agreement](../../Silmaril/Machine/SqliteVfs/FileView/Thms.lean), [retaining mutations](../../Silmaril/Machine/SqliteVfs/PageRead/MutationTrace/Thms.lean), and [completed VFS observations](sqlite-vfs-completed-observation.md) | Strict full-page acquisition, byte agreement with an image view, agreement across retaining traces, and projection of completed exchanges from the existing container model. These are concrete adapter inputs. |
| [Process memory](../../Silmaril/Process/Memory.lean), [semantic arenas](../../Silmaril/Semantics/Arena/Defs.lean), and [abstract model sets](../../Silmaril/Semantics/Region/Abstract/Defs.lean) | Process memory already gives byte-span framing with permissions. Arenas model optional slots independently of addresses. Abstract models use sets of observations. None is needed to define the tree or its lookup. |
| [Wasm B-tree V2](../../Silmaril/WasmSpec/BTree/V2/Defs.lean) | Precedent for distinct owned pages and a page frame. Its abstract nodes carry a physical page number and signed 32-bit keys, store keys in internal nodes, and use a fixed Wasm memory layout. |

## Later page refinement

Start with a profile that represents each node in one page. Parameterize it
by page identity, a full-page observation `observe : State → PageId → Option Bytes`,
and a decoder that takes a page identity and bytes. Its result is either
leaf bindings or a branch of `(divider, childPage)` pairs and a rightmost
page ID. The identity parameter lets a concrete format choose a page-specific
header offset. Keep page geometry, handle or snapshot admission, and other
nonpage observations used by the profile explicit.

Identify node occurrences by root-relative lists of zero-based child slots.
The root is `[]`, a branch with `n` dividers has slots `0` through `n`, and
leaves have no successors. A placement witness assigns a page to each live
position and is injective on those positions. In particular, two identical
subtrees still require distinct pages. The root page is part of the adapter's
input. The page footprint is the image of the live positions under the
placement, together with any auxiliary pages used by the profile, such as a
separate header page. If the profile later admits overflow data, include
those observed pages in the footprint and prove their own admission and
aliasing conditions.

Define `ReprAt profile tree placement state` to require tree validity,
placement admission, and an observation at each assigned page whose decoded
view matches its logical node. For a branch, preserve divider order and
replace each child slot with the page assigned to the extended path. For a
leaf, preserve the ordered bindings. Define the representation set to be
`{ state | ∃ placement, ReprAt profile tree placement state }` for the
same fixed profile and root page. Use the explicit witness for local proofs.

For the frame lemma, assume `ReprAt profile tree placement before`, equality
of `observe before p` and `observe after p` for every `p` in the footprint,
and agreement on the nonpage observations used by admission and decoding.
Prove `ReprAt profile tree placement after` with the same witness. Agreement
includes page presence and all the bytes used by each decoder. A write
corollary can obtain this premise from a write footprint disjoint from the
representation footprint when the backing's mutation contract supplies the
required agreement. For SQLite retaining traces, apply the existing
per-page agreement theorem to each footprint member. This step needs the
retention and handle premises for all observed pages.

A later traversal proof can induct on height. At each accepted full-page
read, identify the decoded node using `ReprAt`, apply `Branch.route_get` to
extend the path, and use `Node.lookup_eq_entries` to identify the final
result. The visited pages form a subset of the representation footprint.
Keep read or decode failure distinct from a successful lookup returning
`none`. Connect accepted reads to the pinned full-page VFS contracts or their
later checked generalization. The SQLite `ReadModel` adapter can then relate
its reference equality lookup to `List.lookup` separately from page access.
This proposal makes no codec, pager, or native execution refinement claim.

Run the checks from the repository root with the pins in
[`lean-toolchain`](../../lean-toolchain) and [`lake-manifest.json`](../../lake-manifest.json).
The examples check two interior levels, multiple dividers, an equal-divider
hit, the rightmost descent, a missing fence key, the empty tree, and
rejection of a child that contains its exclusive lower divider.
[Examples](../../Silmaril/Semantics/BTree/Checks.lean)

```sh
lake build --wfail +Silmaril.Semantics.BTree.Checks
make check CHECK_TARGETS=+Silmaril.Semantics.BTree.Checks
```
