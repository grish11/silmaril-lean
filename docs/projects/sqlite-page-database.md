# SQLite tables over numbered pages

A table pairs a positional schema from the relational table library with a
leaf-oriented B-tree of typed rows. Its placement maps root-relative positions
to page addresses. Its decoder takes the address and stored payload and
produces the existing B-tree node view. This accommodates different placements
and page formats. A database is a supplied catalogue of these table roots over
one array. The model requires distinct table names and disjoint live table pages.
Unclaimed pages are unrestricted. [Table and database API](../../Silmaril/Formats/Sqlite/PageDatabase/Thms.lean)

`Table.rows` uses the existing `Relational.Table` type and keeps the tree's leaf
order. `Table.readModel` exposes the SQLite point-read interface.
`Table.readModel_get` identifies its result with routed lookup on a represented
table. The catalogue and decoders are inputs. File parsing, native pager
behavior, SQL execution and transaction durability are outside this layer.
[Relational table framework](../../Silmaril/Semantics/Relational/Table/Defs.lean) · [SQLite B-tree page format](https://sqlite.org/fileformat2.html#b_tree_pages)

## Shared read/write trace contracts

- `ReadWrite.Access Address Value State` supplies partial reads and writes.
  `ReadWrite.Trace.Replays` takes an initial state and a final state. It checks every
  read against the state at that event and applies writes chronologically.
  `Consistent` requires a final state to exist, and replay determines it uniquely.
  `Validates` also requires the endpoints to satisfy supplied representation
  predicates. `Satisfiable` quantifies over the initial state. `Trace.run`
  checks replay when values have decidable equality. [Shared trace API](../../Silmaril/Semantics/ReadWrite/Thms.lean)
- `Page.Array n A` and `Page.UndefArray n A` are indexed by `Fin n`.
  Traces use zero-based natural addresses, with any address at least `n`
  absent. An in-bounds UNDEF page is allocated and can be written. An attempt
  to read it fails. Neither array permits allocation, deallocation or writes
  beyond its size. The satisfiability predicates quantify over an initial
  array of the given size. `UndefArray.satisfiable_iff` shows the two predicates
  coincide when a total fill exists. [Array API](../../Silmaril/Semantics/Page/Array/Thms.lean)
- `Footprint` includes every touched address. `Defs` includes every written
  address. `Uses` includes addresses read before their first write in the trace.
  An address can be both used and defined. The footprint is the union of
  uses and defs. On concatenation, a write in the prefix removes the
  corresponding suffix use from the combined initial demand. [Dataflow and projection laws](../../Silmaril/Semantics/ReadWrite/Thms.lean)
- `reads` and `writes` retain order and repetition in their respective
  projections. A read-only trace agrees with one unchanged state. The write
  projection of a successful replay preserves the two endpoints. The read
  projection agrees with the initial state when read addresses are disjoint from
  write addresses and writes preserve read observations at other addresses. In
  general a read may depend on a discarded write.
  [Projection regressions](../../Silmaril/Semantics/Page/Trace/Checks.lean)

## Replay and representation laws

| Law | Contract |
| --- | --- |
| `Array.run_embed`, `Array.replays_embed_iff` | Embed every total-array cell as defined before replay, or embed the final result after replay. The executable law includes rejection. |
| `UndefArray.run_memory`, `UndefArray.replays_memory_iff` | The same square for the ordinary store view of a partial array. The view preserves absent, UNDEF and defined slots. |
| `UndefArray.replays_complete` | Filling UNDEF at both endpoints carries a successful partial replay to a total replay. The converse can fail because the fill supplies values at initially UNDEF addresses. |
| `Trace.replays_iff_path`, `Program.Records.run`, `Page.replays_completion` | Replay is a generic labelled path. With a returning program path, it induces the existing page run and its write log. The write log also replays on a valid completed image. |
| `lookupTrace_spec`, `lookupTrace_replays_array`, `lookupTrace_replays_undefArray` | The trace identifies the routed lookup result and stays within the represented tree’s pages. It replays without changing either array. |
| `replays_represents_of_disjoint`, `Table.replays_frame`, `Database.replays_frame` | Writes outside a representation's footprint preserve that representation. |

[Labelled path adapter](../../Silmaril/Semantics/ReadWrite/Labelled/Thms.lean) · [B-tree trace API](../../Silmaril/Semantics/BTreePages/Trace/Thms.lean) · [Page completion model](page-completion.md)

## Process memory

`Process.Memory.byteAccess` instantiates the same API with natural-number byte
addresses and `BitVec 8` values. It uses the existing `readBytes` and
`writeBytes` operations on `Process.Memory`, including mapping permissions,
address bounds and backing reads. Each event touches one byte. A sequence of
events checks each byte independently. `replay_writesWithin` applies the
existing memory frame predicate to the trace's def set, preserving mappings
and all backing bytes outside that set. The examples replay a write followed
by a matching read, reject a stale or unmapped read, and preserve the read
projection at an untouched address.
[Memory adapter](../../Silmaril/Process/Memory/Trace/Thms.lean) · [Memory examples](../../Silmaril/Process/Memory/Trace/Checks.lean)

## Verification

Run with the repository's pinned Lean toolchain.

```sh
targets='+Silmaril.Process.Memory.Trace.Checks +Silmaril.Semantics.Page.Trace.Checks +Silmaril.Semantics.BTreePages.Checks +Silmaril.Formats.Sqlite.PageDatabase.Checks'
lake build --wfail $targets
make check CHECK_TARGETS="$targets"
```
