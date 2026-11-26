# Stateful SQLite Track A read adapter

Import `Silmaril.Machine.SQLite.TrackA.Read.Adapter.Thms`. This adapter uses
`pagerHandler`, `vfsTree`, and `vfsTree_corresponds` from the published
`Read.Interaction` surface of PR #3572 at
`b71f7df50b00679ab5e3784ba694621d54731920`. The concrete read comes from
PR #3555 at `852fe2dcb8628565856abe1074273abd96ce27ff` through that base.
[Concrete read](read-case.md) · [Pager and VFS interaction surface](read-interaction.md)

The staged tree issues a typed Pager acquisition. Its handler supplies the
current file and cache to the existing Pager operation, then records the
returned file and cache and appends the completed exchanges in their
original order. The staged continuation consumes the resulting bytes or
error. The composed execution handles the existing open VFS tree. On an
admitted cold miss the backing handler's actual reply feeds that tree's
page acceptance and VM continuation. It records exchanges as it handles
them. Both paths use `Coalgebra.handle`.
[Typed trees and handlers](../../../Silmaril/Machine/SQLite/TrackA/Read/Adapter/Defs.lean)

- `interpretations_agree` applies to any backing handler, starting file and
  cache, requested slot and page, and `Int64` key. Both handled trees reach
  the exact result, file and cache poststates, and completed exchanges of
  `Read.runStaged`. Those exchanges validate the backing file transition and
  label a complete observation of the open VFS tree under the selected replies.
- `pagerTwice_agrees` runs two calls for the same page and key in one handled
  tree. It returns both leaf results. The second acquisition uses the actual
  poststate of the first, and the final history is the given prefix followed
  by the first call's exchanges and then the second call's exchanges. The new
  suffix validates the ordered file transition from the given file state.
- `pagerTwice_readOnly_cold_warm` assumes equality with the image snapshot,
  an existing page view, a live handle, the admitted read range, a vacant
  owned slot, and successful decoding of the leaf. Both results equal the
  logical lookup and the final history is the singleton full-page exchange.
[Public statements](../../../Silmaril/Machine/SQLite/TrackA/Read/Adapter/Thms.lean)

The fixture runs a single two-call tree over a backing that counts requests.
It checks rowid 42 returning 7 and rowid 41 returning absence. For each key,
only the cold acquisition calls the backing, the warm acquisition uses its
installed slot, and a pre-existing history entry precedes the completed read.
It also checks the composed cold VFS execution. Ordinary I/O errors and short
reads remain typed failures. The pinned C path can proceed with zero-filled
short-read bytes. The comparison concerns the Lean models for a designated
leaf and excludes C or native refinement and multi-page execution.
[Checks](../../../Silmaril/Machine/SQLite/TrackA/Read/Adapter/Checks.lean) · [Pinned C path evidence](https://github.com/hiloopai/silmaril-lean/blob/627432c060169951a08c2454b1c524831ce48793/docs/projects/sqlite-track-a/header-inventory/operations.md)

```sh
lake build --wfail +Silmaril.Machine.SQLite.TrackA.Read.Interaction.Checks \
  +Silmaril.Machine.SQLite.TrackA.Read.Adapter.Checks
make check CHECK_TARGETS=+Silmaril.Machine.SQLite.TrackA.Read.Adapter.Checks
for module in Silmaril.Machine.SQLite.TrackA.Read.Adapter.Defs \
    Silmaril.Proofs.Machine.SQLite.TrackA.Read.Adapter.Correspondence \
    Silmaril.Machine.SQLite.TrackA.Read.Adapter.Thms; do
  SILMARIL_REPLAY_MODULE="$module" lake env lean -DwarningAsError=true \
    tools/compiler-explorer/Replay.lean || exit 1
done
```
