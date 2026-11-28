# SQLite backend components

SQLite's architecture describes one disk file containing separate table and
index B-trees, a Pager that supplies and modifies fixed-size pages and
coordinates transactions, and a VFS that brokers OS operations. This
development checks connections between the corresponding Lean interfaces
for selected read and rollback-journal paths.
[SQLite architecture, B-Tree through OS Interface](https://www.sqlite.org/arch.html)

## Public headers

| Component | State and implementation | Checked relation |
| --- | --- | --- |
| VFS | `VFS.FileMap` selects a byte-level `SqliteVfs.FileState` by exact name. `Opened` qualifies a generation token by that name. `parseOpen` and `openExisting` use the existing bounded backing. The read and rollback VFS signatures reuse dependent replies. | `VFS.open_success` identifies the original entry, exact mode and generation, live poststate and frame for all other paths. `VFS.open_error_preserves` frames the whole map. `SqliteVfs.ReadOnlyProfile`, `ReadWriteProfile` and `Trace.Valid` specify the selected backing and its exchanges. |
| Pager | `PageRead.Page`, `Slot`, `Cache`, `Acquire.acquire`, and `Read.Adapter.PagerState` distinguish page geometry, owned vacancy and residency, and the handler's backing, cache and exchange history. `Pager.LockGrant`, `ReadAccess` and `WriteAccess` state the caller obligations. `Pager.observeInsert` combines the landed write interpreter with explicit slot retirement. | `Read.Adapter.interpretations_agree` and `pagerTwice_agrees` specify the handled poststates. `Pager.observeInsert_ofAccess` identifies the exact run and retires just the matching slot. `Pager.commit_reopens` and `sync_failure_preserves_database` give concrete success and fault poststates. |
| B-Tree | `File.Image` and `File.View` describe the file/page bytes. A tree position is a path from a tree root. `BTreePages.Layout` gives the position a numeric page ID. `Page.MapMemory` maps IDs to absent, undefined or defined page data. `BTree.Tree` and its ordered-map projection describe the abstract rows. `TrackB.Read.leafMemory`, `pageLookup` and `run` instantiate the generic machinery. | `BTreePages.Represents`, `lookup_run_iff` and `lookup_orderedMap_run_iff` give the all-height laws on represented generic trees. `TrackB.Read.leaf_represents` and `page_lookup_run_iff` specialize them to the decoded SQLite leaf. `BTree.opened_read` and `catalog_cold_warm` connect that backend to the typed interpreters. |

A VFS path selects a file, which can contain many tree roots and non-tree
pages. A `File.View` is a range in the encoded file. Pager residency gives a
slot the bytes of a particular file page. The abstract page map stores
decoded page payloads, and the ordered map gives key-to-row lookup for a
valid tree. The bridge constructs the abstract memory from a designated
leaf and supplies representation evidence at height zero. All-height trace
replay also covers represented `Page.UndefArray` states. The caller
selects the root/page. An API that follows SQLite interior-page pointers
from a file root, dispatches among indexes, or proves whole-file
correspondence to a checked catalog is outside this development.
[Headers](../../Silmaril/Machine/SQLite/BTree/Thms.lean) ·
[Pager](../../Silmaril/Machine/SQLite/Pager/Thms.lean) ·
[VFS](../../Silmaril/Machine/SQLite/VFS/Thms.lean) ·
[Track B](sqlite-track-b/read-bridge.md)

## Named open and transaction boundary

The bounded name grammar admits a nonempty ASCII basename made from
letters, digits, underscores, hyphens and periods, excluding `.` and `..`.
A plain basename is accepted with either URI flag. URI opt-in also
admits `file:NAME`, `file:NAME?mode=ro` and `file:NAME?mode=rw`, with exact
case and one optional parameter. With the flag off, the colon fails the
basename grammar. The mode argument is an upper bound on URI modes. A
syntactically valid `rw` with a read-only argument gives `modeEscalation`.
Unsupported spelling gives `unsupportedName`, an absent map entry gives
`missingFile`, and a busy entry or a mode above the backing's limit gives
`backing cannotOpen`. Opening an idle entry leaves its bytes and generation
unchanged. Track A's scoped handler handles closes, retirement and I/O on
the selected file. The map entry and generation together identify the
open file in this model, so two entries can have equal token generations.

The native URI grammar and native open flags have a broader domain.
Authorities (including localhost), separators, percent escapes, NUL,
fragments, other URI parameters (including `vfs`, `cache`, `immutable`
and `nolock`), global URI enablement, create flags, temporary and in-memory
databases, and read-write fallback are outside this grammar. The map has
exact keys and represents existing files. Native VFS registration,
dispatch and filename canonicalization, aliasing, permissions, OS descriptor
reuse, file creation, platform I/O, mmap, device characteristics, randomness
and time are outside the backing contract.
[Named-open implementation](../../Silmaril/Machine/SQLite/VFS/Defs.lean) ·
[Native URI and entry point][uri] · [Native VFS ABI][vfs]

A `LockGrant` is a caller-supplied certificate input for one open identity.
Read access requires a live handle in either mode and a matching shared or
exclusive grant. Write access requires a matching exclusive grant, the
named read-write database backing, a live read-write journal handle scoped
by role, and the old page in the exact cache slot. These predicates state
the admitted execution context. `observeInsert` itself checks the slot
through `Release.release`. Another resident page or an unavailable slot
returns a local release error before selecting a write run. The synthetic
grant has no transition semantics. It represents access already granted
outside this model. Native SHARED/RESERVED/PENDING/EXCLUSIVE transitions,
inter-connection exclusion, busy handlers and retries, shared-cache table
locks, VFS file locks, SQLite connection mutexes and thread scheduling are
outside the checked composition.
[Access definitions](../../Silmaril/Machine/SQLite/Pager/Defs.lean) ·
[Native file lock levels][locks] · [Unix lock path][unix] ·
[B-Tree transaction entry][btree-begin] · [Pager begin][pager-begin]

The write starts after transaction setup on the canonical two-page
integer-table image, with an empty open journal. It admits a new signed
rowid and a packed two-field insert that fits the original root leaf.
The successful selected schedule is journal preimage write, journal sync,
database leaf write, database sync, journal deletion. The concrete
fault-free run preserves the catalogue bytes, reopens to the edited
table, and returns a vacant read-cache slot. An injected journal-sync
error preserves the database bytes and the written journal and also
retires the read-cache slot. This cache retirement is an explicit model
operation over one owned slot. It is separate from the write interpreter's
dirty page and actual backing. The tests reacquire the leaf from each
resulting backing.

The write is the DELETE rollback-journal commit path. Journal framing,
creation and hot-journal recovery, database change counters, savepoints,
explicit rollback/playback, cache eviction or spill, lock upgrades,
concurrent transactions, page splits or allocations, multi-file commit,
WAL/SHM and checkpoints, filesystem durability and every crash/recovery
claim are outside the checked execution. Here sync is a reply that
constrains the order of later operations.
[Selected write contract](sqlite-track-a-write.md) ·
[Native Pager write admission][pager-write] · [Native commit and rollback][pager-commit]

## Composition and observation boundaries

- `BTree.opened_read` starts from a successful named open and a matching
  read grant. On the selected live backing and caller's page/cache input,
  Track A's handled Pager and VFS interpretations return the full
  `TrackB.Read.run` outcome. The actual exchanges validate the backing
  transition and select a finite observation of the open VFS tree.
  Invalid page, short read and leaf decode failure can remain typed
  outcomes under this theorem.
- `BTree.catalog_cold_warm` assumes the D4 `Bound`, `ColdLeaf` and
  `Projected` hypotheses. They fix the supported point statement, plan,
  index-one key binding, caller-assigned page, live handle, admitted range,
  owned vacant slot, backing/image agreement, packed-leaf decoder success
  and agreement with the catalog at that key and column. Determinism of
  the one completed read identifies the D4 and Track B buffers. The same
  bytes decode to the generic memory used by the no-edit Page run. The
  projected row yields the typed read result, then D4's transferred cell.
  Both repeated calls return the same resident cache; only the cold one
  adds a full exchange to the observed history. The D3 equality uses
  storage erasure of the D4 post-connection. `Bridge.execute_corresponds`
  separately covers one bound call including typed read failures.
- Generic Page lookup can stop with UB on undefined page data. Under the
  representation hypothesis, the existing run iff entails a normal
  return and excludes Page UB and divergence for lookup, at any generic
  height. Decoder/range/slot admission and ordinary read or write errors
  live at other interfaces. `Write.no_ub` excludes explicit UB in the
  finite write presentation, including ordinary failure results.
- An open interaction tree admits observations for well-typed replies.
  Membership here selects the path using the supplied handler's actual
  replies. The open observation exposes the result and cache. A separate
  handled observation and `Trace.Valid` record the actual backing
  transition. The checked counterexample `badShortRead` is well-typed
  and violates the VFS short-read zero-fill profile.

[Read composition statements](../../Silmaril/Machine/SQLite/BTree/Thms.lean) ·
[Executable fixtures](../../Silmaril/Machine/SQLite/BTree/Checks.lean) ·
[Track A read map](track-a-reading-map.md) · [Track D handoff](sqlite-track-d/handoff-v1.md)

The stable read effects are `TrackA.Read.Adapter.PagerSignature` and
`TrackA.Read.Interaction.VfsSignature`. The stable write effect is
`SqliteVfs.TrackA.Write.vfs`, with file-role-qualified writes and syncs
and journal deletion. These signatures can be imported without a
concrete handler. The above theorems connect those effects through
selected handlers. The statements do not establish refinement of C,
native VFS implementations, or arbitrary SQLite queries.

## Source pins and reproduction

Implementation references use SQLite 3.54.1 mirror commit
[`57520227c95396ce39ba6ecaac8d475b78dd3964`][sqlite-source]
and Fossil identity `555e07ef33f69a0957d24d8e555b702464a131d6f1607f4c3c1e4551e8e6ca76`.
The downloaded architecture page is recorded separately because its URL
tracks the current documentation.

| Source | SHA-256 of retrieved bytes |
| --- | --- |
| [Architecture](https://www.sqlite.org/arch.html) | `e5e00e53255dc1093fc8c087ff31b84c93dc802366392bda14e3f085776f521a` |
| [`manifest.uuid`][uuid] | `7b5efb6e3d4519a2412aaf3607f463191fab7e9251c49fdb799713fac2d79aa4` |
| [`src/main.c`][uri] | `8b0ec9d5a4b2012f8940a3b12b3e21d6ec80cee045c4b5b63fc1d1c37691badc` |
| [`src/sqlite.h.in`][vfs] | `a66be104bd89782526c11e251b88a92d7aaf91a2bf53460a8a6a3fb4dfb13226` |
| [`src/os.h`][locks] | `2837c7443ac1d54e6c3d81dbbe3c24f4c1c79cd9a282cbf5bce98ad6b538a967` |
| [`src/os_unix.c`][unix] | `7403557ac3e93f90096823fda0d554c680e2ee2739a80cc837a7c76b15d08ac5` |
| [`src/btree.c`][btree-begin] | `c96f2e39d62659d649441a7330d753079056fc5cd1b67ce9489bb1be88b13050` |
| [`src/btree.h`][btree-header] | `2b8e38729097808f00a0513723387d059fe1493d05d89a3cbd98b5faeec7b75b` |
| [`src/pager.c`][pager-begin] | `96d7bb9c4a5a6da0909ce0ab4714311e1ffa5f13007dc4c69f028a2760104ba4` |
| [`src/pager.h`][pager-header] | `dd71356ea0978be3a2eec25bb2c44b1378630a1e1a63c511ee6697fa3e620f62` |
| [`src/pcache.h`][pcache-header] | `7fea70c56696d0a435df09bd7d13c684642905cac22651ea604f613fe9d1c277` |

```sh
lake build --wfail +Silmaril.Machine.SQLite.BTree.Checks
make check CHECK_TARGETS='+Silmaril.Machine.SQLite.BTree.Checks'
SILMARIL_REPLAY_MODULE=Silmaril.Machine.SQLite.BTree.Thms \
  lake env lean -DwarningAsError=true tools/compiler-explorer/Replay.lean
```

[sqlite-source]: https://github.com/sqlite/sqlite/commit/57520227c95396ce39ba6ecaac8d475b78dd3964
[uuid]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/manifest.uuid
[uri]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/main.c#L3133-L3388
[vfs]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/sqlite.h.in#L737-L876
[locks]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/os.h#L90-L155
[unix]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/os_unix.c#L1802-L1985
[btree-begin]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/btree.c#L3835-L3990
[btree-header]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/btree.h
[pager-begin]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/pager.c#L5984-L6076
[pager-write]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/pager.c#L6112-L6187
[pager-commit]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/pager.c#L6527-L6901
[pager-header]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/pager.h
[pcache-header]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/pcache.h
