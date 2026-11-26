# SQLite point-read statements and the stateful executor

The D3 fragment models the typed shape `SELECT column FROM table WHERE rowid = ?1`
on an ordinary rowid table where the `rowid` name denotes its actual rowid. An
invocation has a single named projection and either leaves parameter 1 unbound
or attempts one signed 64-bit integer bind. Imports use
`Silmaril.Semantics.SQLite.Relational` and declarations use
`Silmaril.SQLite.Relational`. [Fragment theorems](../../../Silmaril/Semantics/SQLite/Relational/Fragment/Thms.lean)

## SQLite source

The reference is SQLite **3.54.1**, source ID
`2026-10-16 14:45:20 555e07ef33f69a0957d24d8e555b702464a131d6f1607f4c3c1e4551e8e6ca76`.
The repository's `sqlite3.c` for this release has SHA-256
`0c657666d819f261cc4007526ad57e1669de9949df7a8ea847aa284a2bf0ee52`.
The architecture separates tokenization and parsing, preparation of VDBE
bytecode, and bytecode execution. In the pinned source `sqlite3_prepare_v2`
wraps preparation, `sqlite3_bind_int64` checks the parameter range and
writes an integer, and `OP_SeekRowid` reaches a signed integer table
lookup or takes its miss branch. [Architecture](https://sqlite.org/arch.html) · [Release archive](https://sqlite.org/2026/sqlite-amalgamation-3540100.zip) · [Source ID](../../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L470) · [Prepare](../../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L149388) · [Bind](../../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L95107) · [Seek](../../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L101908)

## Operations and observations

- `Executor.prepare` resolves the supplied reference against the connection's
  catalog and returns a plan with a target and a result column label, or a
  defined preparation error such as an unresolved name. The plan's parameter
  starts unbound. `Prepared.bindInt64` accepts index 1 and replaces its
  binding. Out-of-range indices give the modeled `SQLITE_RANGE` and retain
  the previous binding. [Prepare API](https://sqlite.org/c3ref/prepare.html) · [Bind API](https://sqlite.org/c3ref/bind_blob.html)
- `Executor.run` materializes a fresh synchronous run. An unbound parameter
  is SQL NULL and this equality selects no rows. The abstract executor skips
  the backend call on this path. A bound read can return zero rows, one row,
  or a defined backend error. `SelectResult.cell` distinguishes zero rows
  from a present SQL NULL cell and retains the label in both cases.
  `SelectResult.toOutput` gives the corresponding Track C row observation.
  [Expressions and parameters](https://sqlite.org/lang_expr.html) · [Step API](https://sqlite.org/c3ref/step.html)
- `Executor.execute` orders prepare, optional bind, and run. Preparation and
  binding failures return the input connection. Both success and failure of
  a backend read return its backing and cache poststate and append its
  completed exchanges to the input history. `Executor.executeBatch`
  threads that connection through fresh invocations and stops on the first
  error. Its result retains every preceding successful reply, including
  successful empty results, together with each call's poststate. A failed
  call's poststate is the batch poststate. It has no transaction rollback.
- The read-only catalog and observed session fields persist across the
  whole batch. The session fields are autocommit, direct and total change
  counts, and last insert rowid. Backing and cache can still change.
  [Autocommit](https://sqlite.org/c3ref/get_autocommit.html) · [Direct changes](https://sqlite.org/c3ref/changes.html) · [Total changes](https://sqlite.org/c3ref/total_changes.html) · [Last insert rowid](https://sqlite.org/c3ref/last_insert_rowid.html)
- `CheckedRequest.unsupported` reports a profile rejection as an ordinary
  result of its own. It carries the unchanged connection and has an empty
  UB reason set. The explicit UB model gives no ordinary observation
  and one reason for `HostRequest.bindFinalized`. The catastrophic model
  puts that call at top. SQLite documents a bind on a finalized statement
  as undefined. [Bind API](https://sqlite.org/c3ref/bind_blob.html)

## Dependency boundary

`Profile.Value` takes D1's SQL-visible storage value carrier. The parameter
of this fragment is already an `Int64`, so the executor needs no SQL
affinity conversion. `Profile.Catalog` and `Profile.Ref` take D2's catalog
and reference types. The D2-facing `Executor.resolve` maps the admitted
single-projection reference to a `Plan` or returns the catalog's defined
resolution error. A caller admits the supported rowid table and projection
shape before invoking this API.

`Executor.read` consumes the resolved target, signed key, backing and
cache. Its `ReadOutcome` preserves the typed read result, backing poststate,
cache poststate and completed exchange suffix. The proposed Track A adapter
can map the designated target to the Pager slot and page, call the read
handler, lift the projected cell to the D1 value carrier, and pass through
the file, cache, and ordered exchanges. An absent row remains `ok none`
and the adapter's typed read failures go in the defined run-error channel.
The Track A two-call result preserves both result/cache pairs and uses the
full accumulated exchange history. In D3 the executor owns the single append
of each call's suffix and passes the actual poststate to the next invocation.
The conversion of the adapter's cell carrier and the proof that it realizes
D3's lookup relation belong at the adapter boundary. [Track A adapter pin](https://github.com/hiloopai/silmaril-lean/pull/3623/commits/4d69c29875c1d3ab722ac9ca0a43f8203a845d1b)

## Proof contracts and limits

`Reference.resolves` and `Reference.reads` are independent Track C relations.
`Executor.sound` and `Executor.complete` lift the corresponding component
contracts to the statement and its complete final connection.
`Executor.deterministic` and `Executor.total` apply to the executable graph.
The reference inherits determinism from completeness and totality from
soundness. `Executor.executeBatch_iff` compares the batch with an inductive
stop-or-continue judgment under both component contracts.
`Executor.executeBatch_append` splits execution at any invocation boundary
using the first batch's actual poststate. The fragment embeddings restrict
back to the admitted observations, and refinement lifts through both UB
models with explicit collapse equal to the catastrophic semantics.
[Executor API](../../../Silmaril/Semantics/SQLite/Relational/Executor/Thms.lean) · [Relational contracts](../relational.md)

These are semantic contracts for a fixed read-only catalog and a typed
point-read profile. Native tokenization, SQL-tail handling, schema reprepare,
VDBE step-by-step timing, prepared-statement lifetime, connection error
strings and codes, resource exhaustion, transactions and concurrency are
outside the profile. The `run` operation assumes a fresh plan for the
same connection and stable catalog. The theorems quantify over the supplied
resolver and backend contracts and establish no native SQLite equivalence.

```sh
lake build --wfail +Silmaril.Semantics.SQLite.Relational.Executor.Checks
CHECK_TARGETS="$(make -s scope BASE=origin/main)" make check
```

## Catalog snapshot executor

`Silmaril.Semantics.SQLite.Relational.Executor.Catalog.Thms` instantiates the
executor with D1's `SqlValue` and D2's `Snapshot ValueModel.sqlValue sem`.
This development uses D1 at `e153b6ff27d768b392ab3529743e93e74e8a5046`
and D2 at `5dd76d0c384c4d621fa0c63f3de3a0392bd3286d`.
[Value model](../sqlite-relational-d1.md) · [Catalog model](../sqlite-relational-d2.md)

`CatalogExecutor.execute` takes already normalized names. In the ordinary
rowid-table profile a missing table or column reaches the preparation error
channel. A view, a schema where the predicate's `rowid` spelling fails D2's
`resolvesRowId` check, or a generated projection returns a scope rejection.
Once admitted, the executor resolves a checked table and column ordinal,
finds the matching signed rowid, and returns its cell. D2's checked table
invariant rules out a second hit. `CatalogExecutor.Target.lookup_iff` expresses
the lookup using row membership and absence, and `CatalogExecutor.execute_eq`
covers the whole checked entry point and its final connection.

This executor uses an in-memory snapshot. Its backing and cache observations
are units and its exchange list is empty. The catalog and session fields
are carried by the same D3 connection type. The proposed session and VFS
adapter uses D3's generic executor with different backing, cache and exchange
types. [Snapshot executor](../../../Silmaril/Semantics/SQLite/Relational/Executor/Catalog/Thms.lean)

```sh
lake build --wfail +Silmaril.Semantics.SQLite.Relational.Executor.Catalog.Checks
```
