# Track E handoff v1

This is the Track D interface checked with landed dependencies and the staged
D4 bridge. The [Track D guide](README.md) describes the model, upstream source
reference, observation diagrams and information lost at each boundary. Track E
implementation is outside this handoff.

## Consumer interfaces

| Slice | Commands and representative theorem entry points | Lake check targets |
| --- | --- | --- |
| C foundation | `Silmaril.Relational` supplies indexed rows and aligned columns, packed and dependent databases, `QueryRel` with choice/refinement, materialized `Output`, finite stream observations, and explicit/catastrophic UB. Start with `Silmaril.Semantics.Relational.All`. Relevant laws include `StreamDrains.prefix`, `QueryRel.Refines.observe` and `UB.ExplicitQuery.collapse_extendUB`. [Track C contract](../relational.md) | `+Silmaril.Semantics.Relational.Examples`, `+Silmaril.Semantics.Relational.Table.Examples`, `+Silmaril.Semantics.Relational.Database.Examples`, `+Silmaril.Semantics.Relational.Query.Examples`, `+Silmaril.Semantics.Relational.UB.Examples` |
| D1 values and affinity | `Real.ofBits`, `Value.toSql`, `Value.forgetPointers`, `ValueObject.dup`, `Affinity.ofDeclaredType` and `ColumnType.apply`. Laws include `Value.toSql_ofSql`, `Value.toSql_not_injective`, `Value.forgetPointers_not_injective` and `ColumnType.strict_apply_eq_ok_iff`. [D1](../sqlite-relational-d1.md) | `+Silmaril.Semantics.SQLite.Relational.Value.Examples`, `+Silmaril.Semantics.SQLite.Relational.Affinity.Examples` |
| D2 checked schema, tables and catalog | `ValueModel.sqlValue`, `DeclaredColumnType.resolve`, `TableSchema.findColumn`, `CheckedTable.check`, `Snapshot.ForeignKeysValid`, `eraseDatabase` and `eraseKeepingIdentity`. Use `TableSchema.findColumn_eq_some_iff`, `TableSchema.materialize_restrict_iff`, `CheckedTable.rowsEquivColumns`, `CheckedTable.check_transpose`, `erase_columns`, `erase_constraints` and `recover_eraseKeepingIdentity`. [D2](../sqlite-relational-d2.md) | `+Silmaril.Semantics.SQLite.Relational.Catalog.Examples`, `+Silmaril.Semantics.SQLite.Relational.Catalog.SqlValueExamples` |
| D3 generic statement executor | `Executor.prepare`, `Prepared.bindInt64`, `Executor.run`, `Executor.execute`, `Executor.executeBatch`, `CheckedRequest.denote` and `HostRequest.explicit`. Use `Executor.sound`, `Executor.complete`, `Executor.executeBatch_append`, `Executor.executeBatch_iff`, `CheckedRequest.unsupported_iff` and `HostRequest.collapse_explicit`. [D3](statement-executor.md) | `+Silmaril.Semantics.SQLite.Relational.Executor.Checks` |
| D3 concrete snapshot executor | `CatalogExecutor.classify`, `resolve`, `execute` and `reference`. Use `CatalogExecutor.Target.lookup_iff`, `CatalogExecutor.executor_sound`, `CatalogExecutor.executor_complete` and `CatalogExecutor.execute_eq`. The storage-independent profile observes a unit backing and cache and an empty exchange list. [Concrete executor](statement-executor.md#catalog-snapshot-executor) | `+Silmaril.Semantics.SQLite.Relational.Executor.Catalog.Checks` |
| A read seam | `Silmaril.Machine.SQLite.TrackA.Read.Adapter.Thms` exports `interpretations_agree`, `pagerTwice_agrees` and `pagerTwice_readOnly_cold_warm`. Use `Silmaril.Machine.SQLite.TrackA.Read.Interaction.Thms` for `vfsTree_corresponds`. [Read case](../sqlite-track-a/read-case.md) · [Interaction](../sqlite-track-a/read-interaction.md) · [Stateful adapter](../sqlite-track-a/typed-read-adapter.md) | `+Silmaril.Machine.SQLite.TrackA.Read.Checks`, `+Silmaril.Machine.SQLite.TrackA.Read.Interaction.Checks`, `+Silmaril.Machine.SQLite.TrackA.Read.Adapter.Checks`, `+Silmaril.Proofs.Semantics.TrackA.Interaction.Regression` |
| D4 storage bridge | `Bridge.execute`, `Bridge.transferCell`, `Bridge.forgetStorage`, `Bridge.Bound`, `Bridge.ColdLeaf` and `Bridge.Projected`. `Bridge.execute_corresponds` retains the full observation of a bound call, including typed read failure. `Bridge.execute_cold_warm` gives the exact projected D3 result/connection and retains the full successful same-page pair. [D4](read-bridge.md) | `+Silmaril.Machine.SQLite.Relational.Bridge.Checks` |
| D aggregate | `Silmaril.Semantics.SQLite.Relational.All` for D1–D3 and `Silmaril.Machine.SQLite.Relational.All` for D1–D4. Each consumer imports only its aggregate. The Machine checks selected trace membership alongside full one-call correspondence and backing validity, and exact D3 equality alongside retained batch poststates and a valid exchange. | `+Silmaril.Semantics.SQLite.Relational.Checks`, `+Silmaril.Machine.SQLite.Relational.Checks` |

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

`Read.Adapter.Observes` records membership of a finite typed VFS request/reply
trace ending in `.returned (outcome.result, outcome.cache)` with return type
`Read.Result × PageRead.Cache`. It follows the actual replies from the backing
handler and hides administrative Pager and silent steps. It leaves other
members of the open observation set unconstrained. The handled poststates
carry the backing file separately, and `Trace.Valid` validates the completed
exchange suffix from the starting file to that poststate. Track A supplies
single-call handled agreement, repeated-call file/cache/history threading and
admitted read-only same-leaf cold/warm behavior. The D3 executor equality is
a D4 result under its stated hypotheses. Native SQLite refinement and a
Track C executor refinement from Track A alone are outside this seam.
[Track A observation definition](../../../Silmaril/Machine/SQLite/TrackA/Read/Adapter/Defs.lean) ·
[D4 correspondence](read-bridge.md)

`CatalogExecutor.SqlSnapshot` contains individually checked tables and
catalog metadata. A cross-table foreign-key certificate is a separate D2
observation through `CheckedSnapshot`.

The fixtures exercise value erasure and affinity boundaries, checked catalog
constraints and erasure, point hits and misses, resolution and bind failures,
ordinary scope rejection, batch state threading, and D4 cold/warm and short
reads. D4's fixture uses rowids 42 and 41 on a two-page Lean-written image.
Present NULL and NaN rejection are tested at the transfer boundary. The
erasure fixture gives distinct backing files and size exchanges that project
to the same D3 connection and yield the same lookup. General SQLite query plans,
broader value coercions and collation, SQL write behavior, multi-page
execution and a global file/catalog consistency result remain outside the
checked fragment.

## Source graph and hosted evidence

| Dependency | Landed merge | Exact PR head | Confirmed hosted evidence for that head |
| --- | --- | --- | --- |
| [C #3565](https://github.com/hiloopai/silmaril-lean/pull/3565) | `611702d27cc6e43cbb7f3ec74013246d39d322ef` | `a5a0a51b6795b74527795a1edfa3c34d55b144bc` | [Lean](https://github.com/hiloopai/silmaril-lean/actions/runs/45752990563/job/139685437061) · [CI](https://github.com/hiloopai/silmaril-lean/actions/runs/45752990563/job/139686346143) |
| [D1 #3648](https://github.com/hiloopai/silmaril-lean/pull/3648) | `448bd85d9dfd7992855badbd4048999f05b4e704` | `e153b6ff27d768b392ab3529743e93e74e8a5046` | [Lean](https://github.com/hiloopai/silmaril-lean/actions/runs/45756375554/job/139696015664) · [CI](https://github.com/hiloopai/silmaril-lean/actions/runs/45756375554/job/139696568737) |
| [D2 #3688](https://github.com/hiloopai/silmaril-lean/pull/3688) | `d99abfe5131eec3697fa32e41b7d1b0962bcaac9` | `9fd6af51e118f27d364e07b2021f332e4f0a4c30` | [Lean](https://github.com/hiloopai/silmaril-lean/actions/runs/45761682548/job/139713137335) · [CI](https://github.com/hiloopai/silmaril-lean/actions/runs/45761682548/job/139713785544) |
| [D3 generic #3645](https://github.com/hiloopai/silmaril-lean/pull/3645) | `fb129a1cab5eb2108bb24224943538885b87838a` | `eedbe97f3af123fc7f88773daa4115cad1824dfc` | [Lean](https://github.com/hiloopai/silmaril-lean/actions/runs/45756176205/job/139695688999) · [CI](https://github.com/hiloopai/silmaril-lean/actions/runs/45756176205/job/139696171136) |
| [D3 concrete #3745](https://github.com/hiloopai/silmaril-lean/pull/3745) | `86f7e9bb95c5412fe4bd9c9b2ae6684c3151dacd` | `2c710eda48f3eebf3bbed580f79fe2fa9fd8a40b` | [Lean](https://github.com/hiloopai/silmaril-lean/actions/runs/45763819075/job/139721121498) · [CI](https://github.com/hiloopai/silmaril-lean/actions/runs/45763819075/job/139722029809) |
| [A #3623](https://github.com/hiloopai/silmaril-lean/pull/3623) | `26a59ab4f3131bde9cee45053d678fa5b961886f` | `4994778f84b9bee57c8624e37b2deb618567881c` | [Lean](https://github.com/hiloopai/silmaril-lean/actions/runs/45762825175/job/139716711340) · [CI](https://github.com/hiloopai/silmaril-lean/actions/runs/45762825175/job/139717320159) · [CodeQL](https://github.com/hiloopai/silmaril-lean/runs/139717064245) · [Time budget](https://github.com/hiloopai/silmaril-lean/actions/runs/45762825175/job/139717402167) |

All six merges are ancestors of checked main
`79e3bb503e86dce30ab64426dbfc7b42bea454f1`. The five paths touched by #3623
have the same contents at the A merge, at checked main, and at the earlier
A pin `4d69c29875c1d3ab722ac9ca0a43f8203a845d1b`.

Local verification uses temporary merge
`6955e6c524fab55a999dc9506ade9d2132a87a17`, with checked main as its first
parent and D4 PR head `0044819e6bf9e528e7ad755b21f19dbb62bc9ce7` as its second.
Their merge base is `53cdf8fc7c0c6799e92c19986e4ad702315f123c`. The aggregate
increment directly follows the temporary merge. Its evidence is local to
that assembly. Opening the aggregate PR requires the actual D4 merge pin,
then a replay of the increment against fresh main and fresh scoped checks.
[D4 PR #3774](https://github.com/hiloopai/silmaril-lean/pull/3774) ·
[Pinned D4 head](https://github.com/hiloopai/silmaril-lean/commit/0044819e6bf9e528e7ad755b21f19dbb62bc9ce7)

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

for base in 6955e6c524fab55a999dc9506ade9d2132a87a17 \
    79e3bb503e86dce30ab64426dbfc7b42bea454f1; do
  scoped=$(make -s scope BASE="$base") || exit 1
  targets=$(python3 scripts/ci-targets.py --scoped "$scoped" --full "$(make -s scope)") || exit 1
  make check CHECK_TARGETS="$targets" || exit 1
done
```

The explicit build lists all 91 source and proof module targets, including
every fixture in the inventory. The first scope covers the six-file aggregate
increment. The second covers D4 and the increment relative to checked main.
Full-main CI and native equivalence checks are outside those commands.

The local axiom audit covers the D public `Thms` headers and the Track A adapter
and interaction `Thms` headers. Kernel replay covers the D proof modules and
Track A adapter and interaction correspondence proofs over their imports.
[Axiom policy](../../../policy.toml) · [Replay driver](../../../tools/compiler-explorer/Replay.lean)
