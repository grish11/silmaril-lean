# SQLite global object state

Import `Silmaril.Machine.SQLite.GlobalState.All` for object histories, typed
struct payloads, flat and indexed stores, checked views, the named-file
adapter, and the allocator and handle resource contracts. Use
`Silmaril.Machine.SQLite.Architecture.All` separately for Track E's component
diagram and its Interface, compiler, VM and backend contracts. The global-state
package assembles cross-component state and resource observations. The
architecture aggregate follows the four groups of the diagram.
[Architecture and component map](architecture.md) · [Track E coverage](coverage-v1.md)

## Where to start

| Task | Lean import | Guide |
| --- | --- | --- |
| Classify identities and read the ordered VFS roots | `Silmaril.Machine.SQLite.GlobalState.Thms` | [Identities and views](#identities-and-views) |
| Keep live and zombie objects, tombstones, and checked component views | `Silmaril.Machine.SQLite.GlobalState.Store.Thms` | [Presence and erasure](#presence-and-erasure) |
| Observe raw allocation records alongside object histories | `Silmaril.Machine.SQLite.GlobalState.Store.Allocator.Thms` | [Visibility and storage](#visibility-and-storage) |
| Read selected source fields through kind-indexed maps | `Silmaril.Machine.SQLite.GlobalState.StructThms` | [Source fields and indexed maps](object-structs.md) |
| Convert between indexed and flat field-bearing snapshots | `Silmaril.Machine.SQLite.GlobalState.Flat.Thms` | [Dependent flat map](object-state-payloads.md) |
| Use typed structs as state payloads | `Silmaril.Machine.SQLite.GlobalState.StatePayload` | [Struct-to-state bridge](object-state-payloads.md) |
| Follow a Pager's named main file into a read premise | `Silmaril.Machine.SQLite.GlobalState.StructObservations` | [Named-file adapter](object-structs.md#checked-laws-and-adapter) |
| Specify initialized public allocator calls and ownership | `Silmaril.Machine.SQLite.Allocator.Thms` | [Allocator model and replay](allocator-resources.md) |
| Specify handle lifetimes and a read-only default VFS borrow | `Silmaril.Machine.SQLite.Handle.Thms` | [Handle and VFS model and replay](handle-resources.md) |
| Compose resource steps and preserve untouched observations | `Silmaril.Semantics.Resource.Thms` | [Reusable resource API](allocator-resources.md#reusable-resource-api) |

The source reference is SQLite **3.54.1**, Fossil check-in
`555e07ef33f69a0957d24d8e555b702464a131d6f1607f4c3c1e4551e8e6ca76` and mirror commit
`57520227c95396ce39ba6ecaac8d475b78dd3964`. The source inventory gives the
amalgamation checksum and field-by-field source locations.
[Release and source pin](object-structs.md#source-pin) · [Pinned C API][api]

## Identities and views

`ObjectStore ObjectId` is a finite `Std.ExtHashMap` of kinds with
caller-supplied IDs. `ObjectStore.ext` identifies maps with equal lookups,
and `hasKind_unique` checks unique classification. `VfsRoots` records ordered,
distinct references classified as VFS objects in the same snapshot.
`defaultVfs` gives the head if present. A connection's selected VFS is a
separate object reference established by open. [Registry][registry] · [Connection open][open]

`KindView.supports` selects kinds from the whole present snapshot.

| View | Kinds |
| --- | --- |
| `.vfs` | `vfs`, `file` |
| `.publicHandles` | `connection`, `statement`, `blob`, `backup` |
| `.cache` | `pageCache`, `pager`, `file` |
| `.btree` | `btree`, `pager` |

VFS and cache share `file` because Pager uses VFS file-handle storage.
Cache and B-tree share `pager` because `BtShared` references Pager.
Membership is by kind. An unregistered VFS may appear in the VFS view,
and a file unrelated to a particular Pager may appear in the cache view.
Exact reachability needs roots, links and a snapshot invariant. A
`pageCache` object describes `PCache`, while Track E's `PageRead.Cache`
observes slots. [Pager layout][pager-layout] · [B-tree fields][btree] · [Cache fields][cache]

## Presence and erasure

`Objects ObjectId Payload` carries the present object's kind, state and
`Payload kind`. `History ObjectId Payload` also records tombstones.

| State at an ID | History lookup | Objects-only lookup |
| --- | --- | --- |
| Live | `some (.present object)`, state `.live` | `some object` |
| Zombie | `some (.present object)`, state `.zombie` | `some object` |
| Freed | `some (.freed kind)` | `none` |
| Never issued in this history | `none` | `none` |

An optional field can be `none` inside a present object. That null
reference is distinct from missing lookup, a freed ID, and the separate
question of whether a non-null reference resolves. `Objects.lookupLive`
selects ordinary live entries. `PresentId` includes zombies of supported
kinds. `checkId_isSome`, `lookup_get` and `lookup_kind_get` connect its
checked reads to the source object and projected kind map. The source
describes why `sqlite3_close_v2` can keep a zombie connection allocated
while outstanding resources are released. [Close contract][close-api] · [Zombie disposal][zombie]

- `History.lookup_toObjects` and `Objects.lookup_toKinds` describe the
  finite erasures. `History.toObjects_map`, `Objects.map_restrict` and
  `Objects.toKinds_restrict` commute payload erasure and the view filters.
- `History.updatePresent` keeps ID and kind while changing the state and
  payload of a proven present entry. The lookup laws for allocate, update
  and free preserve every unrelated ID. `fresh_allocate_iff`,
  `fresh_updatePresent_iff` and `fresh_free_iff` describe the remaining
  fresh IDs. A freed token remains reserved in the retained history.
- `History.toObjects_free` equates erasing a newly written tombstone
  with deleting the binding in the objects-only store.
  `History.toObjects_not_injective` shows why that projection loses the
  distinction between freed and never issued.
- `IndexedStore.lookup_erasePayloads` and `hasKind_erasePayloads_iff`
  relate indexed lookups and kind membership. The typed value comes from
  the original store. `ObjectFields Ref` parameterizes the top-level
  references and the stores use `LocalFields = ObjectFields LocalId`.
  `IndexedStore.lookup_toFlat` and `FlatStore.lookup_toIndexed` preserve
  typed lookups, including missing entries, across the two field-bearing
  representations. `IndexedStore.lookup_toObjects` and
  `FlatStore.lookup_toObjects` carry the exact payload and caller-supplied
  state. `FlatStore.lookup_toStates_toKinds` agrees pointwise with the
  kind at the original flat key. [Struct-to-state bridge](object-state-payloads.md)

## Visibility and storage

`AllocatorStore ObjectId AllocId Payload Live Tombstone` combines separate
object and raw allocation histories. `StoreId.object` and
`StoreId.allocation` keep the observations distinct even when their
underlying values coincide. `AllocatorStore.lookup_toObjects` erases raw
blocks and object tombstones. `checkObjectId_allocation` also excludes
raw IDs from checked component admission. The raw lane distinguishes a
missing token, live metadata and a freed token. Its insertion laws give
the edited binding and every other lookup.

Visibility and the right to release storage are separate facts. SQLite's
`sqlite3PagerOpen` carves a Pager, PCache and file-handle storage out of one
allocation. An object can therefore have its own identity without having a
separate allocation. A contract can relate objects to the backing block and
state which references own, retain or borrow it. A retained history reserves
abstract lifetime tokens. Native memory may reuse an address after release.
A later address model can pair it with a generation and prove how tokens
relate to addresses. A native null allocator result carries no token and
differs from a failed lookup of an existing token.
[Pager layout][pager-layout] · [Allocator API][allocation-api] · [Field ownership inventory](object-structs.md#source-fields-and-their-lean-projections)

## Resource contracts and refinement boundary

The reusable `Silmaril.Semantics.Resource.Thms` interface is re-exported
through `Allocator.Thms` and `Handle.Thms`. `Contract.Frames` preserves
a chosen key observation outside the writes for the input and reply.
`Contract.seq` passes the first reply into the second operation and
concatenates their write lists, so `Contract.seq_frames` preserves keys
outside both. `Contract.Frames.assertion_iff` additionally requires the
predicate to depend only on declared read keys disjoint from those writes.
A predicate about a reference and its target needs the relevant
observations for both. An unrelated-key map frame alone gives no guarantee
about the lifetime of a referenced object.

`Allocator.State` specializes the raw lane with family, owner, and
requested and usable sizes. `Allocator.frames` uses full tagged store
lookup, and `objects_preserved` preserves the entire object history.
`malloc_success_lookup` establishes freshness and ownership.
`realloc_failure_preserves` keeps the original block on a failed positive
resize, and `realloc_success_lookup` distinguishes in-place resize from a
move that retires the old token. [Allocator model and replay](allocator-resources.md)

`Handle.Payload` supplies lifecycle metadata for connection, statement,
blob and backup kinds and retains the supplied payloads for the other
kinds. `Handle.Step` acts on object history. `Handle.contract` lifts it
to the same tagged store as the allocator, and `Handle.frames` uses that
same full lookup. `open_error_close_only` admits a failed open's cleanup
handle within this profile. `final_dependent_reaps_zombie` retires the
last blocker and its zombie connection under the release premises.
`stale_not_fresh` preserves the distinction between a retired token and
a fresh one. A backup's source blocks close. The profile reserves its
distinct, live, ready destination through finish.
`close_borrowed_inapplicable` rules out closing that destination while
borrowed, and `backup_finish_destination` checks and preserves its state.
The default VFS borrow uses a caller-supplied registry of live VFS entries.
`find_default_iff` gives its unchanged history and `find_default_live`
gives presence of a non-null result. [Handle and VFS model and replay](handle-resources.md)

The verified algebra concerns finite lookup, erasure and modeled
transitions. The source guides justify the choice of observations.
Native refinement remains open. It needs a mapping from concrete
addresses and fields to object and allocation identities, with generation
invariants for later address reuse, and a simulation of the relevant C
implementations. The allocator contract observes extents and ownership.
A byte-memory refinement would also have to prove the preserved prefix
on a successful resize. The selected
`IndexedStore.namedMainFile` adapter uses a supplied backing-local handle.
`NamedMainFile.readAccess` requires `VFS.Opened.Live` and a read grant to
produce `Pager.ReadAccess`. Interface/D3 observations still describe the
admitted point-query profile. ABI layout, platform locks, registry mutation
and named VFS search, shared-cache
ownership, WAL/SHM and general SQLite execution remain separate from
these proofs. [Source inventory](object-structs.md) · [Track E behavioral coverage](coverage-v1.md#behavioral-coverage)

## Build, replay and evidence

Use the pinned [Lean toolchain](../../../lean-toolchain) and
[Lake manifest](../../../lake-manifest.json). The aggregate fixture imports
only `GlobalState.All`. It checks the indexed and flat lookups of a typed
VFS descriptor, then follows it through the state and kind bridge to
the default root. It follows a successful malloc with a read-only
default VFS borrow. The allocation and object share an underlying ID
value, and the composed frame preserves the full object lookup. Erasure
excludes the raw block from checked object admission.

```bash
set -euo pipefail
root=Silmaril.Machine.SQLite.GlobalState
allocator=Silmaril.Machine.SQLite.Allocator
handle=Silmaril.Machine.SQLite.Handle
resource=Silmaril.Semantics.Resource
lake build --wfail +"$root".{AggregateChecks,Checks,Store.Checks} \
    +"$root".{Store.Allocator.Checks,StructChecks,StatePayloadChecks} \
    +"$allocator".Checks +"$handle".Checks
for check in Silmaril/Machine/SQLite/GlobalState/{AggregateChecks,Checks,Store/Checks,Store/Allocator/Checks,StructChecks,StatePayloadChecks}.lean \
    Silmaril/Machine/SQLite/{Allocator,Handle}/Checks.lean; do
  lake env lean -DautoImplicit=false -DwarningAsError=true "$check"
done
make check CHECK_TARGETS=+"$root".AggregateChecks
for module in "$root".{All,AggregateChecks,Defs,Roots,Thms,Checks} \
    "$root".Store.{Defs,Thms,Checks,Allocator.Defs,Allocator.Thms,Allocator.Checks} \
    "$root".Flat.{Defs,Thms} \
    "$root".{Structs,Indexed,StructThms,StructObservations,StructChecks,StatePayload,StatePayloadChecks} \
    Silmaril.Proofs.Machine.SQLite.GlobalState.{Store.Erasure,Indexed,Flat.Lookup} \
    "$allocator".{Defs,Thms,Checks} Silmaril.Proofs.Machine.SQLite.Allocator.Laws \
    "$handle".{Defs,Thms,Checks} Silmaril.Proofs.Machine.SQLite.Handle.Laws \
    "$resource".{Defs,Thms} Silmaril.Proofs.Semantics.Resource.Laws; do
  SILMARIL_REPLAY_MODULE="$module" lake env lean -DwarningAsError=true \
    tools/compiler-explorer/Replay.lean
done
```

The [driver](../../../tools/compiler-explorer/Replay.lean) replays each
named module against its imports. The leaf check modules print their
public theorem dependencies for comparison with [the axiom policy](../../../policy.toml).
The exact-head CI runs below contain successful hosted Lean, aggregate CI
and time-budget jobs. The replay counts cover the modules reported for
each increment, with reproduction commands in its guide. The aggregate's
local replay and exact-head CI receipt is in [integration PR #4235][pr4235].

| Increment | Merge | Exact PR head | CI and kernel replay |
| --- | --- | --- | --- |
| [Kind store and roots #4179][pr4179] | `6b7c38807e1a65a7e7db2aca9b2db14b8ea450b7` | `2d772052ee99a47ce14ec7c0b2fc7704f529496c` | [CI][ci4179] · 4 modules · [Replay][replay4179] |
| [Finite history and views #4195][pr4195] | `78691a894605c94c0448039454f7af20729a8424` | `8ad353aaf1e2b1a2858e9fd8472cc6ea9d855fe6` | [CI][ci4195] · 8 modules · [Replay][replay4195] |
| [Structs and indexed store #4202][pr4202] | `a621f14437fe129710eb5b8219897afcce8c9f48` | `46f1bc26c238b0088458c77fdf9e2b2e464e8621` | [CI][ci4202] · 6 modules · [Replay][replay4202] |
| [First struct/state bridge #4218][pr4218] | `73089cef088fe86eaeebf69d24ebbba4375db373` | `de3ed0cedf63daf83bfdb2b1f75052fbe3b948f5` | [CI][ci4218] · 2 modules · [Replay][replay4218] |
| [Raw blocks and object updates #4223][pr4223] | `01a39e10e1f80ea53a21c517dc67289fa02a37be` | `1b8cc147d75a596e95aec1053cfd46b8aebc6ff3` | [CI][ci4223] · 11 modules · [Replay][replay4223] |
| [Allocator and Resource API #4198][allocator-pr] | `c337f7ca0de0efbbd2ec9f4dced3da203bc9107f` | `744fd86fcc88726306ab80c7674d7e584a20dc12` | [CI][ci4198] · [168.2 s of 300][budget4198] · 7 modules and 20 axiom audits · [Replay](allocator-resources.md#build-and-replay) |
| [Parametric structs and flat bridge #4234][pr4234] | `be3143e6840903217cec8797359eafee5ae6005f` | `70ab775cde8fb0386174909b32a84ad24ecb585e` | [CI][ci4234] · [138.0 s of 300][budget4234] · 11 modules · [Replay](object-state-payloads.md) |
| [Handle and default VFS #4251][pr4251] | `fce01929e4dd115bd9cfe75d7ed3e2b189feb8da` | `e798acfbbbf5a3fa6861b1884b6cfa858cfab737` | [CI][ci4251] · [176.8 s of 300][budget4251] · 4 modules and 23 axiom audits · [Replay](handle-resources.md#build-and-replay) |

[api]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/sqlite.h.in
[registry]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/os.c#L352-L447
[open]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/main.c#L3624-L3645
[close-api]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/sqlite.h.in#L319-L357
[zombie]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/main.c#L1396-L1439
[allocation-api]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/sqlite.h.in#L3260-L3339
[pager-layout]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/pager.c#L4923-L4954
[btree]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/btreeInt.h#L345-L460
[cache]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/pcache.c#L26-L54
[allocator-pr]: https://github.com/hiloopai/silmaril-lean/pull/4198
[ci4198]: https://github.com/hiloopai/silmaril-lean/actions/runs/45810337339
[budget4198]: https://github.com/hiloopai/silmaril-lean/actions/runs/45810337339/job/139878042412
[pr4179]: https://github.com/hiloopai/silmaril-lean/pull/4179
[ci4179]: https://github.com/hiloopai/silmaril-lean/actions/runs/45805693035
[replay4179]: https://github.com/hiloopai/silmaril-lean/blob/2d772052ee99a47ce14ec7c0b2fc7704f529496c/docs/projects/sqlite-track-e/global-object-state.md#replay
[pr4195]: https://github.com/hiloopai/silmaril-lean/pull/4195
[ci4195]: https://github.com/hiloopai/silmaril-lean/actions/runs/45807432264
[replay4195]: https://github.com/hiloopai/silmaril-lean/blob/8ad353aaf1e2b1a2858e9fd8472cc6ea9d855fe6/docs/projects/sqlite-track-e/global-object-state.md#replay
[pr4202]: https://github.com/hiloopai/silmaril-lean/pull/4202
[ci4202]: https://github.com/hiloopai/silmaril-lean/actions/runs/45807957033
[replay4202]: https://github.com/hiloopai/silmaril-lean/blob/46f1bc26c238b0088458c77fdf9e2b2e464e8621/docs/projects/sqlite-track-e/object-structs.md#replay
[pr4218]: https://github.com/hiloopai/silmaril-lean/pull/4218
[ci4218]: https://github.com/hiloopai/silmaril-lean/actions/runs/45809205966
[replay4218]: https://github.com/hiloopai/silmaril-lean/blob/de3ed0cedf63daf83bfdb2b1f75052fbe3b948f5/docs/projects/sqlite-track-e/object-state-payloads.md
[pr4223]: https://github.com/hiloopai/silmaril-lean/pull/4223
[ci4223]: https://github.com/hiloopai/silmaril-lean/actions/runs/45809436655
[replay4223]: https://github.com/hiloopai/silmaril-lean/blob/1b8cc147d75a596e95aec1053cfd46b8aebc6ff3/docs/projects/sqlite-track-e/global-object-state.md#replay
[pr4234]: https://github.com/hiloopai/silmaril-lean/pull/4234
[ci4234]: https://github.com/hiloopai/silmaril-lean/actions/runs/45811000129
[budget4234]: https://github.com/hiloopai/silmaril-lean/actions/runs/45811000129/job/139880218087
[pr4251]: https://github.com/hiloopai/silmaril-lean/pull/4251
[ci4251]: https://github.com/hiloopai/silmaril-lean/actions/runs/45813726561
[budget4251]: https://github.com/hiloopai/silmaril-lean/actions/runs/45813726561/job/139891800681
[pr4235]: https://github.com/hiloopai/silmaril-lean/pull/4235
