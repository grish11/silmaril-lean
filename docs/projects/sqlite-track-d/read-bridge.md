# Track D4 point-read bridge

Import `Silmaril.Machine.SQLite.Relational.Bridge.Thms`. Declarations are in
`Silmaril.SQLite.Relational.Bridge`. The bridge lives in Machine because it
uses both the Machine read adapter and the Semantics statement executor.
[Definitions](../../../Silmaril/Machine/SQLite/Relational/Bridge/Defs.lean) · [Public theorems](../../../Silmaril/Machine/SQLite/Relational/Bridge/Thms.lean)

## Pinned inputs

- Track A's stateful adapter from PR #3623 at
  `4d69c29875c1d3ab722ac9ca0a43f8203a845d1b`.
  [Adapter contract](../sqlite-track-a/typed-read-adapter.md) · [Commit](https://github.com/hiloopai/silmaril-lean/commit/4d69c29875c1d3ab722ac9ca0a43f8203a845d1b)
- Track D3's catalog integration at `c1ff954cf62ff228357470fad3c152c1f1941478`
  includes PR #3645 at `eedbe97f3af123fc7f88773daa4115cad1824dfc` and D2 at
  `5dd76d0c384c4d621fa0c63f3de3a0392bd3286d`. Track C's merged foundations
  are at `611702d27cc6e43cbb7f3ec74013246d39d322ef`.
  [Statement executor](statement-executor.md) · [Catalog model](../sqlite-relational-d2.md) · [Relational foundations](../relational.md)

The source reference is SQLite **3.54.1**, source ID
`2026-10-16 14:45:20 555e07ef33f69a0957d24d8e555b702464a131d6f1607f4c3c1e4551e8e6ca76`.
The repository amalgamation has SHA-256
`0c657666d819f261cc4007526ad57e1669de9949df7a8ea847aa284a2bf0ee52`.
SQLite separates VDBE execution, B-tree lookup, page acquisition and the
file-system interface. The pinned integer `OP_SeekRowid` calls
`sqlite3BtreeTableMoveto`. The Pager's main-file branch in `readDbPage`
reads a full page at `(pgno - 1) * pageSize` through `sqlite3OsRead`, which
calls the file's `xRead` method.
[Architecture](https://sqlite.org/arch.html) · [Release archive](https://sqlite.org/2026/sqlite-amalgamation-3540100.zip) · [Seek source](../../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L101908) · [Pager source](../../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L62034) · [VFS source](../../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L27753)

## Correspondence

The input is a fresh D3 point-read invocation with normalized names and a
successful signed 64-bit bind to parameter 1. `Bound` records D3's scope
classification, catalog resolution to a plan, and supplied binding. The caller
maps the plan target to the correct slot and page of an already-open backing.
Track A's VM reads the second field of the designated packed rowid leaf.

- `execute_corresponds` starts from D3's actual preparation and binding. The
  executor calls the composed Track A read, and A's one-call theorem relates
  that run to the typed Pager tree and the handled and open VFS tree. The
  bridge carries the plan label or typed run error, the input catalog and
  session, and the actual returned backing and cache. The completed VFS
  exchanges extend the input history in order. The theorem validates the
  new suffix against the backing handler even on a read failure.
- `execute_cold_warm` requires `ColdLeaf` for snapshot identity, page geometry,
  a live handle, the read range, the vacant slot and successful leaf decoding.
  `Projected` compares the input leaf lookup with the checked catalog at the
  bound key and requires that the catalog select the second field. A leaf
  miss requires absence in the catalog. A hit requires
  conversion of the projected field and a catalog row with that key and value.
  Both cases use D3's `Target.Matches` lookup contract.
  Track A's cold/warm lookup and two-call adapter theorems give the two actual
  Pager returns. D3's batch has the installed cache and the same catalog and
  session in both poststates, with one completed page read after the original
  prefix. `CatalogExecutor.execute_eq` gives equality with the catalog-only
  executor on the result and final connection after `forgetStorage` erases
  the backing, cache and exchanges.

`ReadFailure.trackA` retains the full acquisition, leaf or VM error. Absence
and a present SQL NULL stay distinct. Integers, blob bytes and admitted
binary64 bits transfer directly. The text conversion re-encodes decoded
characters as UTF-8, so original text-encoding bytes and tags are outside the
observation. `ReadFailure.nanReal` rejects a NaN bit pattern that D1 cannot
represent as a REAL. These bridge errors carry no mapping to native status
codes. A short read remains a typed error with its completed exchange, while
the pinned C Pager path can continue with zero-filled short-read data.
[`xRead` contract](https://sqlite.org/c3ref/io_methods.html) · [`sqlite3_step` contract](https://sqlite.org/c3ref/step.html)

The theorems concern the two Lean interfaces at the bounded same-page read.
The caller supplies the physical location and the decode and catalog
agreement at the key. Schema parsing, general projections, B-tree descent,
cache invalidation, locking, WAL, statement lifetime and native SQLite
refinement are outside their scope.

## Checks

The fixture writes a two-page image through the existing Lean writer and
uses a checked catalog snapshot for `sample.amount`. It checks rowid 42
returning 7, absent rowid 41, cold/warm cache and exchange history, and a
short read that returns a changed backing state. It also covers an unbound
parameter, an out-of-range bind, a present NULL and NaN rejection.
[Checked examples and axiom audit](../../../Silmaril/Machine/SQLite/Relational/Bridge/Checks.lean)

```sh
lake build --wfail +Silmaril.Machine.SQLite.Relational.Bridge.Checks \
  +Silmaril.Machine.SQLite.TrackA.Read.Adapter.Checks \
  +Silmaril.Semantics.SQLite.Relational.Executor.Catalog.Checks
# Set BASE to the ref or commit used as the base of the D4 diff.
CHECK_TARGETS="$(make -s scope BASE="$BASE")" make check
```
