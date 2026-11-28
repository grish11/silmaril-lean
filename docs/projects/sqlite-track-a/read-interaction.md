# SQLite Track A read interaction

The adapter is in `Silmaril.Machine.SQLite.TrackA.Read.Interaction`. It
reuses the standalone read case from PR #3555 and the interaction foundation
from PR #3543 at `61d4a44f4514730e0779c4180a768abc21086ed7`. The `Machine`
region's declared dependencies include `Semantics`.
[Standalone read case](read-case.md) · [Pinned interaction API](https://github.com/hiloopai/silmaril-lean/blob/61d4a44f4514730e0779c4180a768abc21086ed7/Silmaril/Semantics/TrackA/Interaction/Defs.lean) · [Region map](../../../regions.toml)

## Checked correspondence

- `vfsTree_corresponds` applies to any existing `SqliteVfs.Handler`, input
  file and cache, slot, page and integer key. The staged exchanges validate
  the file transition. The open `vfsTree` has a completed observation of
  those exact request/reply pairs and returns the staged search result and
  cache. A vacant, admitted miss exposes the actual page read as a visible
  node. The reply feeds `PageRead.accept` and the VM leaf continuation. A
  matching cache hit or local rejection returns without a visible node.
- `vfsTree_readOnly_cold_warm` needs matching backing and image bytes, an
  existing page view, a live handle and admitted read range, an owned vacant
  slot, and successful leaf admission to the stated table. Both observations
  return the same `Read.lookupValue` and installed cache. The cold observation
  includes the completed read with its full bytes. The warm observation has
  zero exchanges.
- `handledPager_returns_staged` uses `Coalgebra.handle` to answer the VM's
  typed acquisition request with `PageRead.Acquire.acquire`. Its returned
  value is the full staged outcome, including the final file and cache and
  completed VFS exchanges. The handled Pager request is silent in this
  tree's observation. The open `vfsTree` exposes VFS exchanges as visible
  edges at the lower boundary.
[Public theorem statements](../../../Silmaril/Machine/SQLite/TrackA/Read/Interaction/Thms.lean) · [Typed adapters](../../../Silmaril/Machine/SQLite/TrackA/Read/Interaction/Defs.lean)

The VFS tree is open to other replies of the request's type. The theorem
selects the reply supplied by the given backing handler. The scope is a
single target-page acquisition and one `SeekRowid` with a local payload.
I/O errors and short reads are ordinary results. `PageRead.fill` rejects a
short read and retains its completed exchange. The pinned C main-file
branch can admit a zero-filled buffer. The C evidence motivates the
complete-read cut on an admitted 512-byte leaf. The theorems compare Lean
models and leave C and native refinement, transaction setup, and multi-page
SQL execution outside their scope.
[Pinned source notes from PR #3531](https://github.com/hiloopai/silmaril-lean/blob/627432c060169951a08c2454b1c524831ce48793/docs/projects/sqlite-track-a/header-inventory/operations.md)

## Reproduction

The checks build the concrete fixtures and audit the three public
interaction theorems. Kernel replay rechecks the named modules over their
imported `.olean`s.

```sh
lake build --wfail +Silmaril.Machine.SQLite.TrackA.Read.Interaction.Checks
make check CHECK_TARGETS=+Silmaril.Machine.SQLite.TrackA.Read.Interaction.Checks
for module in Silmaril.Machine.SQLite.TrackA.Read.Interaction.Defs \
    Silmaril.Proofs.Machine.SQLite.TrackA.Read.Interaction.Correspondence \
    Silmaril.Machine.SQLite.TrackA.Read.Interaction.Thms; do
  SILMARIL_REPLAY_MODULE="$module" lake env lean -DwarningAsError=true \
    tools/compiler-explorer/Replay.lean || exit 1
done
```
