# Track E handoff v1

This is the Track D interface at the staged D4 source graph. For the model,
upstream source reference, observation diagrams and information lost at each
boundary, see the [Track D guide](README.md). Track E implementation is outside
this handoff.

## Consumer interfaces

| Slice | Commands and representative theorem entry points | Lake check targets |
| --- | --- | --- |
| C foundation | `Silmaril.Relational` supplies indexed rows and aligned columns, packed and dependent databases, `QueryRel` with choice/refinement, materialized `Output`, finite stream observations, and explicit/catastrophic UB. Start with `Silmaril.Semantics.Relational.All`. Relevant laws include `StreamDrains.prefix`, `QueryRel.Refines.observe` and `UB.ExplicitQuery.collapse_extendUB`. [Track C contract](../relational.md) | `+Silmaril.Semantics.Relational.Examples`, `+Silmaril.Semantics.Relational.Table.Examples`, `+Silmaril.Semantics.Relational.Database.Examples`, `+Silmaril.Semantics.Relational.Query.Examples`, `+Silmaril.Semantics.Relational.UB.Examples` |
| D1 values and affinity | `Real.ofBits`, `Value.toSql`, `Value.forgetPointers`, `ValueObject.dup`, `Affinity.ofDeclaredType` and `ColumnType.apply`. Laws include `Value.toSql_ofSql`, `Value.toSql_not_injective`, `Value.forgetPointers_not_injective` and `ColumnType.strict_apply_eq_ok_iff`. [D1](../sqlite-relational-d1.md) | `+Silmaril.Semantics.SQLite.Relational.Value.Examples`, `+Silmaril.Semantics.SQLite.Relational.Affinity.Examples` |
| D2 checked schema, tables and catalog | `ValueModel.sqlValue`, `DeclaredColumnType.resolve`, `TableSchema.findColumn`, `CheckedTable.check`, `Snapshot.ForeignKeysValid`, `eraseDatabase` and `eraseKeepingIdentity`. Use `TableSchema.findColumn_eq_some_iff`, `TableSchema.materialize_restrict_iff`, `CheckedTable.rowsEquivColumns`, `CheckedTable.check_transpose`, `erase_columns`, `erase_constraints` and `recover_eraseKeepingIdentity`. [D2](../sqlite-relational-d2.md) | `+Silmaril.Semantics.SQLite.Relational.Catalog.Examples`, `+Silmaril.Semantics.SQLite.Relational.Catalog.SqlValueExamples` |
| D3 generic statement executor | `Executor.prepare`, `Prepared.bindInt64`, `Executor.run`, `Executor.execute`, `Executor.executeBatch`, `CheckedRequest.denote` and `HostRequest.explicit`. Use `Executor.sound`, `Executor.complete`, `Executor.executeBatch_append`, `Executor.executeBatch_iff`, `CheckedRequest.unsupported_iff` and `HostRequest.collapse_explicit`. [D3](statement-executor.md) | `+Silmaril.Semantics.SQLite.Relational.Executor.Checks` |
| D3 concrete snapshot executor | `CatalogExecutor.classify`, `resolve`, `execute` and `reference`. Use `CatalogExecutor.Target.lookup_iff`, `CatalogExecutor.executor_sound`, `CatalogExecutor.executor_complete` and `CatalogExecutor.execute_eq`. The storage-independent profile observes a unit backing and cache and an empty exchange list. [Concrete executor](statement-executor.md#catalog-snapshot-executor) | `+Silmaril.Semantics.SQLite.Relational.Executor.Catalog.Checks` |
| Provisional A read seam | `Read.runStaged`, `Read.runComposed`, `Read.Interaction.vfsTree`, `Read.Adapter.pagerTree` and `pagerTwice` under `Silmaril.Machine.SQLite.TrackA`. The adapter theorems are `interpretations_agree`, `pagerTwice_agrees` and `pagerTwice_readOnly_cold_warm`. [Read case](../sqlite-track-a/read-case.md) · [Interaction](../sqlite-track-a/read-interaction.md) · [Stateful adapter](../sqlite-track-a/typed-read-adapter.md) | `+Silmaril.Machine.SQLite.TrackA.Read.Checks`, `+Silmaril.Machine.SQLite.TrackA.Read.Interaction.Checks`, `+Silmaril.Machine.SQLite.TrackA.Read.Adapter.Checks`, `+Silmaril.Proofs.Semantics.TrackA.Interaction.Regression` |
| D4 storage bridge | `Bridge.execute`, `Bridge.transferCell`, `Bridge.forgetStorage`, `Bridge.Bound`, `Bridge.ColdLeaf` and `Bridge.Projected`. `Bridge.execute_corresponds` retains the full observation of a bound call, including typed read failure. `Bridge.execute_cold_warm` gives the exact projected D3 result/connection and retains the full successful same-page pair. [D4](read-bridge.md) | `+Silmaril.Machine.SQLite.Relational.Bridge.Checks` |
| D aggregate | `Silmaril.Semantics.SQLite.Relational.All` for D1–D3 and `Silmaril.Machine.SQLite.Relational.All` for D1–D4. Each consumer imports only its aggregate. The Machine consumer checks the exact D3 equality, retained batch poststates and valid exchange together. | `+Silmaril.Semantics.SQLite.Relational.Checks`, `+Silmaril.Machine.SQLite.Relational.Checks` |

A caller comparing representation-preserving operations can keep D2's schema,
row identity and SQL storage value or use its checked row/column equivalence.
A caller comparing point-result behavior can use the D3 catalog relation or
the executable equality in `Bridge.execute_cold_warm`. Under `Bound`,
`ColdLeaf` and `Projected`, `CatalogExecutor.execute sem (forgetStorage db) call`
returns exactly `(.statement (.ok result), forgetStorage after)`, where both
D4 calls return `result` and `after`. The D3 call retains the result label and
cell, catalog and session. The D4 observation retains the actual backing,
resident cache and original exchange history extended by one valid full-page
exchange. The equality is for the read-only same-page pair with a
caller-supplied location and agreement at the bound key. Use
`Bridge.execute_corresponds` for the handled Pager/VFS correspondence of a
single bound call, including typed read failures. Defined statement outcomes
and scope rejection have their own channels before the host-level UB comparison.

`CatalogExecutor.SqlSnapshot` contains individually checked tables and
catalog metadata. A cross-table foreign-key certificate is a separate D2
observation through `CheckedSnapshot`.

The fixtures exercise value erasure and affinity boundaries, checked catalog
constraints and erasure, point hits and misses, resolution and bind failures,
ordinary scope rejection, batch state threading, and D4 cold/warm and short
reads. D4's fixture uses rowids 42 and 41 on a two-page Lean-written image.
Present NULL and NaN rejection are tested at the transfer boundary. There is
no native differential run in this handoff. General SQLite query plans,
broader value coercions and collation, SQL write behavior, multi-page
execution and a global file/catalog consistency result remain outside the
checked fragment.

## Source graph and hosted evidence

| Component | Exact source and status |
| --- | --- |
| C | Landed in main at `611702d27cc6e43cbb7f3ec74013246d39d322ef`. The successful hosted Lean job was on the PR head `a5a0a51b6795b74527795a1edfa3c34d55b144bc`. [Merged PR #3565](https://github.com/hiloopai/silmaril-lean/pull/3565) · [Lean job](https://github.com/hiloopai/silmaril-lean/actions/runs/45752990563/job/139685437061) |
| D1 | Input `e153b6ff27d768b392ab3529743e93e74e8a5046` landed at `448bd85d9dfd7992855badbd4048999f05b4e704`. The Lean job covers the cited PR head. [Merged PR #3648](https://github.com/hiloopai/silmaril-lean/pull/3648) · [Lean job](https://github.com/hiloopai/silmaril-lean/actions/runs/45756375554/job/139696015664) |
| D2 | Staged input `5dd76d0c384c4d621fa0c63f3de3a0392bd3286d`, with D1 as its parent. Local assembled coverage. [Source](https://github.com/hiloopai/silmaril-lean/commit/5dd76d0c384c4d621fa0c63f3de3a0392bd3286d) |
| D3 generic | Input `eedbe97f3af123fc7f88773daa4115cad1824dfc` landed at `fb129a1cab5eb2108bb24224943538885b87838a`. The Lean job covers the cited PR head. [Merged PR #3645](https://github.com/hiloopai/silmaril-lean/pull/3645) · [Lean job](https://github.com/hiloopai/silmaril-lean/actions/runs/45756176205/job/139695688999) |
| D3 concrete | Staged input `c1ff954cf62ff228357470fad3c152c1f1941478`, whose parent `0786fd798057955fa492fcab966590221cfc108d` joins the D3 generic head (first parent) and D2 (second parent). Local assembled coverage. [Source](https://github.com/hiloopai/silmaril-lean/commit/c1ff954cf62ff228357470fad3c152c1f1941478) |
| A seam | Provisional input `4d69c29875c1d3ab722ac9ca0a43f8203a845d1b`, with its own hosted run against the A interaction branch. Its source ancestry contains `61d4a44f4514730e0779c4180a768abc21086ed7` (interaction foundation), `e482b51e919e8c55d992dcda54550be9196fe8c9` (single-leaf read), `b71f7df50b00679ab5e3784ba694621d54731920` (typed interaction), and `0cbb7d0f16d64ca945a10a6ceecf12dff45e41be` (handler interpretation). [PR #3623](https://github.com/hiloopai/silmaril-lean/pull/3623) · [Lean job](https://github.com/hiloopai/silmaril-lean/actions/runs/45754003904/job/139688464305) |
| D4 assembled base | `2f78b894acb0e661350d3367e100b25b333bdd90` has ordered parents `d3aea2aef2b50d7c06f4c9e9eccd7eb68e9f94da` (then-main, including C), A seam and D3 concrete. [Merge source](https://github.com/hiloopai/silmaril-lean/commit/2f78b894acb0e661350d3367e100b25b333bdd90) |
| D4 bridge and aggregate | Original D4 `986d168a201a1c4e421847be7803189b55978810` is a one-parent increment on the assembled base. Its direct follow-up `fe9952c12c81bc56258999633f6aae406f5741ae` strengthens the logical projection, and is the sole parent of the aggregate increment. Local assembled coverage. [Original bridge](https://github.com/hiloopai/silmaril-lean/commit/986d168a201a1c4e421847be7803189b55978810) · [Projection follow-up](https://github.com/hiloopai/silmaril-lean/commit/fe9952c12c81bc56258999633f6aae406f5741ae) |

Hosted jobs above apply to the cited source PR revisions. The D2, concrete D3,
D4 and aggregate evidence here is local to the assembled source graph.
The aggregate carries the provisional A seam solely through its staging
ancestry. Main at `e684c3070c9d547fe638baf4ce2bd32930513a2c` contains C,
D1 and generic D3. The D2, concrete D3, A seam and D4 pins are staged.

For landing, D2 follows the merged D1, and concrete D3 follows D2 and the
merged generic D3. The Semantics entry can then be reviewed against the landed
core. The Machine entry and bridge require the landed A read surface. Repin to
landed dependencies on fresh main and repeat the scoped checks before opening
a main PR for those files.

## Local reproduction

From the repository root after applying the aggregate increment, use the
pinned Lean nightly `nightly-2026-11-05` at
`67dafde474fbaf278d6d7f822068549bf6e532fa`. The repository manifest pins
Mathlib and CSLib at `569134c2fc750d92baa85d50cd925a7e20a93dd2`.
Use the Covalence scoper installed by the repository's CI action.
[Manifest](../../../lake-manifest.json) · [Scoper pin](../../../.github/actions/lake-cache-tool/action.yml)

```bash
paths=(
  Silmaril/Semantics/{Relational,SQLite/Relational,TrackA/Interaction}
  Silmaril/Machine/SQLite/{Relational,TrackA/Read}
  Silmaril/Proofs/Semantics/{Relational,SQLite/Relational,TrackA/Interaction}
  Silmaril/Proofs/Machine/SQLite/{Relational,TrackA/Read}
)
mapfile -t targets < <(rg --files -g '*.lean' "${paths[@]}" |
  sed -e 's/\.lean$//' -e 's@/@.@g' -e 's/^/+/' | sort)
lake build --wfail "${targets[@]}"

for base in fe9952c12c81bc56258999633f6aae406f5741ae \
    d3aea2aef2b50d7c06f4c9e9eccd7eb68e9f94da; do
  scoped=$(make -s scope BASE="$base") || exit 1
  targets=$(python3 scripts/ci-targets.py --scoped "$scoped" --full "$(make -s scope)") || exit 1
  make check CHECK_TARGETS="$targets" || exit 1
done
```

The explicit build passed for 91 source and proof module targets, including
all the fixtures in the inventory. Both repository checks passed. The first
selected two targets for the aggregate increment. The second selected 12 for
the assembled staging diff from its then-main parent. Full-main CI and native
equivalence checks are outside those commands.

Local `#print axioms` checks covered all 80 theorem declarations in the D
public `Thms` headers and the A adapter `Thms` header. The observed axioms
were within `policy.toml`. The kernel replay driver rechecked the ten D proof
modules and the A adapter correspondence proof over their imports.
[Axiom policy](../../../policy.toml) · [Replay driver](../../../tools/compiler-explorer/Replay.lean)
