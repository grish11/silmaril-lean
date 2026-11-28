# SQLite 3.54.1 operation paths and proof interfaces

The paths below use the Linux `unix` VFS with private cache, normal locking,
mmap disabled, and an ordinary on-disk rowid table. The rollback-journal
profile uses `journal_mode=DELETE` and `synchronous=FULL`. The WAL comparison
uses its own journal mode. These are selected paths through the pinned
source, with runtime observations for the fixtures listed below.
[Source identity and interface inventory](README.md) · [SQLite architecture](https://sqlite.org/arch.html)

## Rowid lookup

Use a prepared `SELECT v FROM t WHERE rowid=42` on a table declared
`t(rowid INTEGER PRIMARY KEY, v INTEGER)`. Consider an integer key and a
cold target page with a local record payload in the main database file.
[Rowid code generation][seek-codegen] · [VM execution][vm-seek]

1. `sqlite3_step` reaches `sqlite3Step` and `sqlite3VdbeExec`. The
   statement's `OP_Transaction` calls `sqlite3BtreeBeginTrans`. On the path
   that opens a read transaction and needs page 1, `btreeBeginTrans` calls
   `lockBtree`, which calls `sqlite3PagerSharedLock` and acquires page 1.
   File-lock acquisition can dispatch through `sqlite3OsLock` → `xLock`.
   Header or file-version reads can precede the target-page lookup.
   [Step][api-step] · [Transaction opcode][vm-transaction] · [B-Tree transaction][btree-trans] · [Page 1 and shared lock][btree-lock] · [Pager shared lock][pager-lock] · [OS adapters][os-dispatch]
2. `OP_OpenRead` opens a B-Tree cursor via `sqlite3BtreeCursor`.
   `OP_SeekRowid` follows the shared `OP_NotExists` body on the integer
   path and calls `sqlite3BtreeTableMoveto`. A cursor that needs its root
   reaches `moveToRoot` → `getAndInitPage`. For an interior page, the
   search chooses the child pointer associated with a cell or the rightmost
   child pointer and uses `moveToChild` → `getAndInitPage`.
   [Open cursor][vm-open] · [Seek opcode][vm-seek] · [Root and child movement][btree-move] · [Table search][btree-seek]
3. `getAndInitPage` calls `sqlite3PagerGet`. The Pager's `xGet` selects
   `getPageNormal` in this profile. After cache lookup, a miss on an
   existing ordinary page reaches `readDbPage` → `sqlite3OsRead` →
   `file->pMethods->xRead`. With the POSIX Unix method table this is
   `unixRead`, which reads at `(pgno - 1) * pageSize` for one page.
   Its underlying read path can use positional I/O or seek and read,
   depending on the platform build. On a short read, `unixRead` zero-fills
   the unread suffix and returns `SQLITE_IOERR_SHORT_READ`, as required by
   the VFS contract. The main-file branch of `readDbPage` converts that code
   to `SQLITE_OK`. Page-format admission still applies to the resulting bytes.
   [Page acquisition][btree-acquire] · [Getter selection][pager-getter-select] · [Pager dispatch][pager-get-dispatch] · [Normal getter][pager-normal] · [OS adapters][os-dispatch] · [Unix methods][unix-methods] · [Unix system calls][unix-read-io] · [Unix short read][unix-short-read] · [VFS short-read contract][vfs-short-read] · [Pager main-file result][pager-main-read]
4. On a match, `OP_Column` can read the on-page record via
   `sqlite3BtreePayloadFetch` and `OP_ResultRow` exposes the row. A
   successful negative or positive comparison jumps to P2 for the selected
   seek. An empty tree also yields a negative comparison. An I/O or
   corruption error follows the error path. The comparison out value and
   the C return code therefore have different meanings.
   [Seek outcomes][vm-seek] · [Payload borrow][btree-payload] · [Column decode][vm-column] · [Result row][vm-row]

### Read alternatives

| Condition | Change to the path |
| --- | --- |
| Target-page cache hit | With `PAGER_GET_NOCONTENT` clear, `getPageNormal` can return an initialized cached page before calling `readDbPage`. Transaction setup can still perform VFS reads. A cursor already on the requested key can also return before page acquisition. [Cache hit][pager-cache-hit] · [Pager shared lock][pager-lock] · [Table seek fast paths][btree-seek] |
| mmap enabled, eligible page and no covering WAL frame | `getPageMMap` can use `sqlite3OsFetch` → `xFetch` for a page above page 1 when the Pager is in `PAGER_READER` or the request has `PAGER_GET_READONLY`. A successful null mapping falls back to the normal getter. A fetch error is returned. The mapped-page release path uses `xUnfetch`. [mmap getter][pager-mmap] · [Mapped release][pager-map-release] · [OS fetch adapters][os-fetch] |
| Snapshot has a WAL frame for this page | `readDbPage` uses `sqlite3WalFindFrame` and `sqlite3WalReadFrame`. The latter returns the result of `sqlite3OsRead` on the WAL file at the frame payload offset. The Pager propagates a WAL short-read status. If the lookup succeeds with no frame, the Pager reads the main file. WAL read-lock acquisition can call `xShmLock` on the database file through the OS adapter. That namespace and lifetime are distinct from rollback-mode file locks. [Pager read][pager-read] · [WAL frame read][wal-read] · [WAL shared locks][wal-shared] |
| Scan, index or overflow record | `OP_Rewind` can call `sqlite3BtreeFirst`. Index seek uses index cursors and a record comparator. A record whose payload exceeds the local bytes can require overflow-page reads through `accessPayload`; the optional direct overflow read there also explains why the architecture diagram is insufficient as a call graph. [Rewind][vm-rewind] · [Index seek][btree-index] · [Overflow I/O][btree-overflow] |
| Virtual table or in-memory database | `OP_VFilter` / `OP_VUpdate` invoke registered module callbacks. Their storage behavior depends on the module. In a memory database the Pager may supply bytes without reading a disk file. [Virtual table filter][vfilter] · [Virtual table update][vupdate] · [Normal getter][pager-normal] |

## Insert and commit

Use `INSERT INTO t(rowid,v) VALUES(43,8)` in autocommit mode on the same
ordinary table. Select a new row that fits in an existing leaf, with a
single writable database file, no hot journal, no spill and no atomic-write
shortcut. The insert changes cached bytes. The subsequent commit handles
database-file writes.
[Insert code generation][insert-codegen] · [VM insert][vm-insert]

1. `OP_Transaction` starts a B-Tree write transaction. Its new-writer path
   reaches `sqlite3PagerBegin`, which can obtain a RESERVED lock on the main
   file in rollback mode. `OP_Insert` passes a `BtreePayload` and cursor to
   `sqlite3BtreeInsert`. On the selected leaf insertion path,
   `insertCellFast` calls `sqlite3PagerWrite` before modifying the page.
   [VM transaction][vm-transaction] · [Start write transaction][pager-begin] · [VM insert][vm-insert] · [B-Tree insert][btree-insert] · [Leaf insertion][btree-insert-cell]
2. In `PAGER_WRITER_LOCKED`, `pager_write` calls `pager_open_journal`
   before marking the page dirty. If that call fails, `pager_write` returns
   before `sqlite3PcacheMakeDirty`. After the open succeeds, the Pager marks
   the page dirty, then records the old bytes of the existing page if it
   is absent from the rollback journal. A failure writing that record returns
   before the Pager sets `PGHDR_WRITEABLE`. Journal writes go through
   `sqlite3OsWrite` → `xWrite`. Once write admission succeeds, the leaf edit
   changes the cached page image.
   [Open journal][pager-open-journal] · [Write journal record][pager-add-journal] · [Pager write admission][pager-write] · [OS adapters][os-dispatch]
3. Successful top-level `OP_Halt` reaches `sqlite3VdbeHalt` → `vdbeCommit`
   in the selected autocommit case. The single-file branch obtains the
   necessary exclusive lock and calls `sqlite3BtreeCommitPhaseOne` →
   `sqlite3PagerCommitPhaseOne`. The regular rollback path syncs the journal,
   writes dirty pages to the main file via `pager_write_pagelist`, then syncs
   the database. These actions dispatch through `xSync` and `xWrite`. Phase
   two calls `sqlite3BtreeCommitPhaseTwo` → `sqlite3PagerCommitPhaseTwo` →
   `pager_end_transaction`, which finalizes the DELETE journal via VFS
   `xDelete` for this fixture.
   [Halt opcode][vm-halt] · [Autocommit branch][vm-autocommit] · [Single-file commit][vm-commit] · [B-Tree commit phases][btree-commit] · [Pager phase one][pager-commit] · [Pager phase two][pager-commit2] · [Journal finalization][pager-end] · [VFS delete][unix-delete]

WAL commits log changed pages to the WAL using `pagerWalFrames` →
`sqlite3WalFrames`. Checkpointing has a separate path for writing database
pages. Rollback-mode alternatives include a cache spill, journal modes that
finalize by truncating or zeroing a header, and a super-journal for eligible
multi-file transactions. A nonfitting cell can trigger B-Tree balancing,
including page allocation and cursor changes. The selected single-file
trace does not establish durability or crash recovery. Those require a
storage and failure model covering writes, sync, device capabilities,
locking and recovery. [WAL write path][pager-wal] · [WAL checkpoint][wal-checkpoint] · [Spill branch][pager-spill] · [Journal modes][pager-end] · [Multi-file commit][vm-multifile] · [B-Tree balancing branch][btree-insert]

## Reproduction and observations

The fixture uses the vendored amalgamation, GCC 14.2.0 on Linux x86-64 with
`-DSQLITE_THREADSAFE=1 -O0 -g -fno-pie -finstrument-functions`. It links the
instrumented object into a test driver with `-no-pie -lm -ldl -pthread`.
The driver creates the following database, using `unix` and
`SQLITE_OPEN_PRIVATECACHE` on every connection, with a zero mmap limit and
normal locking. It runs `EXPLAIN` for the selected SELECT and INSERT,
closes the setup connection, reopens the database, and records calls during
the first `sqlite3_step` of each indicated statement.

```sql
PRAGMA page_size=4096;
PRAGMA journal_mode=DELETE;
PRAGMA synchronous=FULL;
CREATE TABLE t(rowid INTEGER PRIMARY KEY, v INTEGER);
INSERT INTO t VALUES(42,7);
```

| Fixture | Observed outcome and internal calls |
| --- | --- |
| First `SELECT v FROM t WHERE rowid=42` after reopening | `EXPLAIN` includes `SeekRowid`. The step returns `SQLITE_ROW` with `7`; the target page uses `getPageNormal` → `readDbPage` → `sqlite3OsRead` → `unixRead`. The next step returns `SQLITE_DONE`. |
| Repeat the SELECT on the same connection, then use `rowid=41` | The repeat still returns `7` without a target-page `readDbPage`. The step includes a file-version read from `sqlite3PagerSharedLock`. The absent key gives `SQLITE_DONE` without a row. |
| Selected INSERT after those reads | `EXPLAIN` includes `Insert`; the step returns `SQLITE_DONE`. Calls include `insertCellFast` → `sqlite3PagerWrite`, rollback-journal record writes, `syncJournal`, `pager_write_pagelist`, database sync and `unixDelete`. |
| WAL reader with writer still open | Switch a writer connection to WAL, set `wal_autocheckpoint=0` and execute `UPDATE t SET v=9 WHERE rowid=42`. A separate new private-cache reader returns `9`. The lookup calls `sqlite3WalReadFrame` → `sqlite3OsRead` → `unixRead` and the step includes `sqlite3OsShmLock` → `unixShmLock`. |

`EXPLAIN` identifies emitted opcodes. The native call observations come
from GCC function-entry hooks, resolving callee and return addresses
against `nm -an` for the instrumented test binary. The fixture's database
and the step boundaries limit the observations. Its traces do not
establish the optimized corpus binary's call sequence or the paths for
other builds or inputs.

## Candidate dependent interfaces

These signatures are pseudocode for a future Lean model. A world records
configuration, object identities and their aliasing, transaction and lock
state, and a generation for each invalidatable borrow. An input handle
requires evidence for its object in the current world. Holding multiple
references to a shared page or file is compatible with that model. A
transition that invalidates a generation invalidates all its derived
borrows. Writable buffers need an explicit extent and an overlap policy.
For each admitted request, the reply family is indexed by the before and
after worlds.

```text
Request : World → Type
Reply   : (before : World) → Request before → (after : World) → Type
Runs    : (before : World) → (r : Request before) →
          (after : World) → Reply before r after → List Event → Prop

prepareV2 : (db : LiveDb before) → (sql : ReadableSlice before) →
            ByteCount sql → TailSlotChoice before sql → Request before
tableSeek : (c : ReadableTableCursor before) → Int64 → Request before
pageGet   : (p : PagerReader before) → (n : ValidPageNo p) →
            PageGetFlags p → Request before
pageWrite : (p : PagerWriter before) → PageRef before p → Request before
commitOne : RollbackWriter before → SyncPolicy before → Request before
commitTwo : RollbackCommitReady before → Request before
xRead     : (f : LiveFile before) → (r : FileReadRange f) →
            WritableSlice before r.count → Request before
xLock     : (f : LiveFile before) → UpgradeRequest f → Request before
```

The result families should retain the following distinctions.

| Request | Candidate result and transition |
| --- | --- |
| Prepare, step and close | Prepare can return a fresh statement of the given connection, a null statement on success, or an error with a null statement. A requested tail, when defined, is an offset into the original input slice. A row-producing step gives a borrow tied to a row and conversion generation. Connection close branches include early failure and deferred destruction. |
| B-Tree seek | Successful seek reports an exact match, an ordered neighbor or an empty cursor. The last two possibilities can share the same negative C comparison. The C status and search result are separate. Error replies can leave changed cursor state and carry only the outputs defined on their path. |
| Pager acquisition and release | Success issues a page reference tied to its Pager and page number. The byte view and B-Tree extra storage depend on that reference. Release consumes the corresponding reference in the world. Cache hit, main-file read, WAL read and mmap can have different events for the same abstract page. A failure can change the Pager state, and the definition of the C out slot depends on the path. |
| Page write and rollback commit | The first successful write admission can issue a mutable page view after recording its old bytes. Track dirty and writable as distinct states, since opening the journal and recording the old page can fail at different points. Phase one success establishes the commit-ready state for the selected profile. Phase two success finalizes the journal and ends the Pager's write transaction. Track journal and main-file events by file identity and retain intermediate state on errors. |
| VFS read and lock | Full and short reads expose the requested output extent, with a zero-filled suffix on a short read. An unrelated I/O failure carries only the buffer information guaranteed by that branch. A successful lock changes the file-lock resource according to the implementation. Busy and error replies retain the actual poststate, since a failed upgrade can have acquired a PENDING lock. |
| Callback dispatch | Index a method call by its registered table version, selected method, and live callback context. The callback can change the world or produce a reentrant call when its contract permits one. An owning destructor and an ordinary borrowed context have separate transition rules. |

`Silmaril.Machine.SqliteVfs.Defs` already has request-indexed responses,
file handle generations and completed exchanges. `SqliteVfs.PageRead` and
`SqliteVfs.PageRead.CacheHit` supply owned page-slot and hit models.
`Silmaril.Formats.Sqlite.BTree.Query.ReadModel.Defs` supplies the abstract
keyed lookup law. `Silmaril.Formats.Sqlite.Vdbe` and
`SqliteVfs.FileView.VdbeLeaf` supply a bounded read-only VM and a one-leaf
adapter. The corpus pins a separate native mutex dispatch cut. The ABI
model starts from typed C prototypes. These are reuse points with their
own profiles. Relating C state, page references, SQLite return codes and VFS
calls to these models is a proof obligation.
[VFS contract](../../sqlite-vfs.md) · [Page read](../../sqlite-page-read.md) · [Cache hit](../../sqlite-vfs-cache-hit.md) · [ReadModel definitions](../../../../Silmaril/Formats/Sqlite/BTree/Query/ReadModel/Defs.lean) · [VM leaf adapter](../../sqlite-vfs-vdbe-leaf.md) · [Mutex dispatch](../../sqlite-mutex.md) · [ABI contracts](../../abi.md)

A future module could live at `Silmaril.Machine.SqliteVfs.TrackA.HeaderInterface.Defs`
with a sibling `Thms` header when proofs exist. This placement would allow
reuse of existing Machine and Formats headers under the current region map.
An initial lookup result could relate one admitted leaf, an integer rowid,
and a successful page acquisition to a `ReadModel` result while retaining
the observed VFS calls. A separate write result could relate an admitted
leaf edit and the selected journal trace. A source or native refinement
claim would still require a relation to the pinned C or compiled execution.
This inventory establishes no Lean theorems, end-to-end SQL correctness, or
coverage of SQLite's concurrency and crash recovery.
[Region map](../../../../regions.toml) · [Unix partial lock upgrade][unix-upgrade]

[seek-codegen]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/wherecode.c#L1757-L1770
[insert-codegen]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/insert.c#L2745-L2795
[api-step]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/vdbeapi.c#L910-L1008
[vm-transaction]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/vdbe.c#L4257-L4305
[vm-open]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/vdbe.c#L4541-L4613
[vm-seek]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/vdbe.c#L5620-L5703
[vm-column]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/vdbe.c#L3047-L3143
[vm-row]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/vdbe.c#L1807-L1853
[vm-rewind]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/vdbe.c#L6524-L6574
[vm-insert]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/vdbe.c#L5897-L5985
[vm-halt]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/vdbe.c#L1350-L1423
[vfilter]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/vdbe.c#L8671-L8737
[vupdate]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/vdbe.c#L8886-L8940
[vm-autocommit]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/vdbeaux.c#L3417-L3462
[vm-commit]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/vdbeaux.c#L2947-L3043
[vm-multifile]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/vdbeaux.c#L3045-L3185
[btree-lock]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/btree.c#L3312-L3337
[btree-trans]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/btree.c#L3725-L3758
[btree-acquire]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/btree.c#L2409-L2443
[btree-move]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/btree.c#L5486-L5649
[btree-seek]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/btree.c#L5813-L5979
[btree-index]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/btree.c#L6061-L6158
[btree-payload]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/btree.c#L5430-L5477
[btree-overflow]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/btree.c#L5252-L5358
[btree-insert]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/btree.c#L9441-L9717
[btree-insert-cell]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/btree.c#L7460-L7531
[btree-commit]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/btree.c#L4343-L4461
[pager-lock]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/pager.c#L5290-L5503
[pager-getter-select]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/pager.c#L1041-L1055
[pager-get-dispatch]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/pager.c#L5786-L5808
[pager-read]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/pager.c#L3075-L3128
[pager-main-read]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/pager.c#L3093-L3099
[pager-cache-hit]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/pager.c#L5629-L5635
[pager-normal]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/pager.c#L5597-L5698
[pager-mmap]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/pager.c#L5703-L5769
[pager-map-release]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/pager.c#L4159-L4185
[pager-begin]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/pager.c#L5984-L6042
[pager-open-journal]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/pager.c#L5893-L5968
[pager-add-journal]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/pager.c#L6053-L6100
[pager-write]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/pager.c#L6127-L6175
[pager-commit]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/pager.c#L6652-L6740
[pager-commit2]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/pager.c#L6764-L6810
[pager-end]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/pager.c#L2090-L2219
[pager-spill]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/pager.c#L4668-L4731
[pager-wal]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/pager.c#L3225-L3288
[wal-read]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/wal.c#L3722-L3759
[wal-checkpoint]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/wal.c#L2281-L2430
[wal-shared]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/wal.c#L1111-L1160
[os-dispatch]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/os.c#L88-L112
[os-fetch]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/os.c#L193-L209
[unix-methods]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/os_unix.c#L5816-L5859
[unix-read-io]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/os_unix.c#L3463-L3505
[unix-short-read]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/os_unix.c#L3550-L3579
[vfs-short-read]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/sqlite.h.in#L847-L852
[unix-delete]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/os_unix.c#L6836-L6876
[unix-upgrade]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/os_unix.c#L1973-L2094
