# SQLite object structs and indexed store

This increment adds fields for the nine kinds in [the kind store](global-object-state.md).
Import `Silmaril.Machine.SQLite.GlobalState.StructThms` for the fields,
indexed maps, kind erasure, and their laws. Import
`Silmaril.Machine.SQLite.GlobalState.StructObservations` for the selected
named-file read adapter. The [Track E baseline][coverage] describes the
Architecture, Interface/D3, VFS, Pager, and B-tree observations.

## Source pin

The reference is SQLite **3.54.1**, `SQLITE_VERSION_NUMBER = 3054001`,
source ID `2026-10-16 14:45:20 555e07ef33f69a0957d24d8e555b702464a131d6f1607f4c3c1e4551e8e6ca76`.
The official archive `sqlite-amalgamation-3540100.zip` has SHA-256
`0a9c8e34352dad46006aa82836d5383bff9dc6bc9ce5a60553c05aa30e6ad1f9`.
The split source links use the GitHub mirror of that Fossil check-in.
[Release pin][release] · [Generated API][header] · [Fossil manifest][manifest] · [Mirror][mirror]

## Source fields and their Lean projections

Ownership here means disposal responsibility in the source. A retaining
reference keeps a particular resource available through a source mechanism
such as a count or an outstanding statement. Borrowed references rely on
another lifetime, and intrusive links record membership. The Lean field types
record kind, scope and optionality. The indexed map laws apply even to field
values whose references lack a corresponding entry.

- **Connection and backends.** A public `sqlite3*` denotes a connection
  allocation. `ConnectionFields.vfs` borrows its selected descriptor after
  open. `firstStatement` records the optional `pVdbe` list head.
  `BackendSlot` records an `aDb` element’s schema name and optional owned
  `Btree` handle. The array starts at embedded `aDbStatic` and can move on
  ATTACH. Schema names are logical selectors. The TEMP schema is
  connection-owned, and ordinary `Db.pSchema` borrows schema storage owned
  by `BtShared`. Mutexes, error `Mem`, parse context, client-data and
  savepoint lists are outside these fields.
  [Connection fields][connection] · [Backend and schema][db] · [Array growth][db-grow]
- **Statements and cursors.** A `sqlite3_stmt*` denotes the `Vdbe` itself.
  Reprepare replaces contents while retaining the public handle. `db`
  points back to the owner. `StatementLink` distinguishes `ppVPrev`
  pointing to the connection's head slot from pointing into its predecessor.
  `next` represents nullable `pVNext`. The list includes inactive statements.
  The selected `apCsr` slots hold optional scoped `BtreeCursorFields`.
  A selected `BtCursor` is contained in the VDBE cursor block and borrows its
  `Btree`. Its root page is a logical page number and its current/parent
  pages stand for held Pager references. The slot number, page number and
  cursor storage have separate meanings. Opcode arrays, registers, frames,
  result-row aliases, and the sorter and virtual-table cursor variants are
  deferred. `KeyInfo` is an index-specific borrow and `CellInfo.pPayload`
  is a byte view.
  [Statement fields][vdbe] · [List insertion][vdbe-link] · [Reprepare][reprepare] ·
  [Cursor allocation][vdbe-cursor] · [B-tree cursor][btcursor] · [Cell view][cell]
- **Incremental blob.** A public `sqlite3_blob*` denotes an `Incrblob`
  allocation. It borrows `db` and the database name, manages cleanup of its
  private `pStmt`, and borrows `pCsr` through statement cursor slot zero.
  `BlobFields.statement` can be absent after invalidation. Its schema name,
  column, offset and size describe the selected value. Reopening can change
  the row while retaining the blob handle. `pTab` and byte-buffer ownership
  remain at the source boundary.
  [Incrblob][blob] · [Cursor and invalidation][blob-cursor] · [Reopen][blob-reopen]
- **Backup.** Public init allocates one `sqlite3_backup`, borrows both
  connections, and increments the source B-tree’s `nBackup` to retain the
  source backend. `destinationBtree` starts absent and is set after a
  destination write transaction begins in step. The destination schema
  is a copied name. `BackupNotification` makes `pNext` meaningful only
  after the source Pager attaches the backup. The internal stack backup
  with a null `pDestDb` is deferred.
  [Backup fields][backup] · [Init][backup-init] · [Destination][backup-step] ·
  [Notification list][backup-attach] · [Internal copy][backup-copy]
- **VFS roots.** The registry borrows descriptors supplied to `vfsList`
  and links them using `pNext`. The default is the head of that list. The kind
  core’s `VfsRoots` represents this order. Register moves an object to the
  head for `makeDflt` or an empty list and inserts it after the head otherwise.
  Unregister unlinks it, and existing selected references can still name it.
  The descriptor’s name is its lookup key. The descriptor reference selects
  actual methods and configuration.
  [VFS ABI][vfs] · [Registry operations][registry]
- **Selected VFS and files.** Main open resolves an explicit name or the
  registry default, with an admitted URI `vfs=` override, then stores that
  descriptor in the connection. ATTACH performs its own lookup with the
  connection VFS name as fallback. `PagerFields.vfs` records the Pager's
  borrowed selection, also used for its journal and WAL operations. File
  control returns that Pager VFS. Global sleep looks up the current default.
  `VfsFields` represents descriptor metadata. `sqlite3_file` is
  caller-supplied storage of size `szOsFile`, and its nullable `pMethods`
  borrows shared methods. `FileFields.openMode` captures open versus
  unopened storage in the selected profile. Allocation, open lifetime,
  filename, and any underlying OS descriptor or inode are distinct.
  Unix inode/SHM state and the `memdb` delegate and shared stores are
  implementation-specific.
  [URI override][uri] · [Main open][open] · [ATTACH][attach] · [Pager VFS][pager-vfs] ·
  [File control][fcntl] · [Sleep][sleep] · [File API][file] · [Close][os-close] ·
  [Unix file][unix] · [Unix inode][inode] · [memdb VFS][memdb]
- **Pager.** A Pager contains the `PCache` and three `sqlite3_file`
  subobjects in its allocation. Their role references are required in
  `PagerFields`, even when individual file slots are unopened. The
  optional backup head is a borrowed notification list. The optional
  `Wal`, journal bitset, savepoint array and scratch storage are
  Pager-managed. WAL borrows the main file and has its own file storage.
  [Pager fields][pager] · [Contained objects][pager-layout] · [Wal][wal]
- **Buffered cache.** `PCache` owns the pluggable `sqlite3_pcache`. The
  default implementation is `PCache1` with hash chains of `PgHdr1` and a
  private or shared `PGroup` whose LRU links unpinned entries. The API
  page is a leading member of `PgHdr1`. Its buffer supplies `PgHdr.pData`,
  and its extra storage contains `PgHdr`, followed by the typed
  `MemPage` view in B-tree use. `PageCacheFields` records selected
  buffered headers by scoped slot, retaining page number, content, refcount
  and optional dirty links. The default implementation can rekey or recycle
  allocations. Logical page identity is backing plus page number.
  `PgHdr.pPage` is absent for the separate mmap path.
  [Core cache][pcache] · [Default cache][pcache1] · [Recycling][recycle] ·
  [Dirty links][pghdr] · [Header placement][pghdr-init] · [MemPage view][mempage] ·
  [Mmap variant][mmap]
- **B-tree.** A `Btree` is a connection-local backend handle. `BtShared`
  owns the Pager and lazily allocated schema, and retains a nullable
  page-one reference. Shared-cache lookup can reuse it by full path and VFS
  pointer. `BtreeContent` scopes selected fields to the handle in the
  nonshared profile. `BtreeFields.sourceBackupCount` records the counter
  used at close. The shared cursor list, writer alias, `BtLock` list, and
  sharing/refcount transitions are deferred.
  [B-tree structures][btree] · [Share lookup][sharing] · [Release][bt-close]

Optional native references are represented with `Option` within the
admitted object phases. The tagged sum for backup notifications also
distinguishes an unattached backup from an attached last list node. Scoped
slots cover contained or aliased storage such as `Db`, `VdbeCursor`,
`BtCursor`, `PgHdr`, and `MemPage`. The nonshared `BtShared` projection
avoids introducing a global identity until sharing is modeled. Generic
callback arguments, destructor data, text, scalar/link-slot addresses and
byte ranges carry no object IDs. The built-in `memdb` lower VFS is an
example where a specific implementation establishes a typed reference
behind `pAppData`. [memdb initialization][memdb]

## Close behavior in the source

`sqlite3_close` returns `SQLITE_BUSY` when the statement head is nonempty or
an attached B-tree has a nonzero source backup count. Both close APIs run
virtual-table cleanup before the busy check. `close_v2` enters zombie state
even when busy. The release gate requires zombie state and a clear busy
predicate. Accepted close drops the client-data registrations before that
gate. [Public close contract][close-api] · [Close and busy predicate][close] ·
[Zombie gate][zombie] · [Source backup count][backup-count]

Public finalize resets and unlinks the statement before checking for
zombie release. Blob close frees its wrapper and calls public finalize on
the saved private statement. A cleared statement takes `finalize(NULL)`,
which is a no-op. A blob read/write abort can use the internal finalizer
without running the release gate. Backup finish decrements the source
count, unlinks its notification entry if attached, rolls back any
applicable destination transaction and checks release on the destination
and source. The API reserves the destination until finish, and a
destination-only backup contributes no busy count there.
[Public finalize][finalize] · [Blob close][blob-close] · [Blob abort][blob-abort] ·
[Internal finalize][internal-finalize] · [Backup finish][backup-finish] · [Backup API][backup-api]

## Checked laws and adapter

`ObjectFields Ref` describes references in a caller-selected kind-indexed
family. `IndexedStore` uses the `LocalId` instance and stores a finite ordered
map per kind, keyed by `LocalId.slot` with value type `LocalFields kind`.
`TaggedId` combines the kind and slot, so equal numeric slots in different
kinds compare unequal. This concrete encoding needs no disjointness
hypothesis. The kind view folds the finite tagged keys into the existing
`ObjectStore`. `lookup_erasePayloads` identifies erased lookup with
mapping a successful typed lookup to its tag. `hasKind_erasePayloads_iff`
recovers a successful lookup in the original indexed store from kind
membership. The payload value comes from that original store. Insert and
erase commute with the corresponding kind-store edit and preserve typed
lookups at every other tagged ID.

`IndexedStore.namedMainFile` follows the Pager’s main-file reference and
requires a named open file entry. It projects to `VFS.Opened` with the
supplied backing-local handle, plus mode and page size.
`NamedMainFile.readAccess` uses existing `Opened.Live` and lock-grant
premises to produce `Pager.ReadAccess` for the resulting `PageRead.Page`.
The regression composes this with the existing successful named-open
theorem. Open generation, file bytes and lock authority come from that
model and the caller.

The first scope is the connection/statement links, the VFS/Pager/file
selection, and one buffered B-tree path. Blob and backup fields record
their different retention mechanisms for later resource rules. The
state-layer adapter and flat snapshot conversion are described separately.
Defer allocator and identity histories, presence and lifetime
invariants, state-level views, operational close transitions, ABI offsets,
callback dynamics, shared cache, custom cache policies, mmap/WAL/SHM,
and general multipage/index/overflow behavior.
[State payload and flat snapshot guide](object-state-payloads.md)

## Replay

```sh
root=Silmaril.Machine.SQLite.GlobalState
lake build --wfail +"$root".StructChecks
lake env lean -DautoImplicit=false -DwarningAsError=true \
  Silmaril/Machine/SQLite/GlobalState/StructChecks.lean
for part in Structs Indexed StructThms StructObservations StructChecks; do
  SILMARIL_REPLAY_MODULE="$root.$part" \
    lake env lean -DwarningAsError=true tools/compiler-explorer/Replay.lean || exit 1
done
SILMARIL_REPLAY_MODULE=Silmaril.Proofs.Machine.SQLite.GlobalState.Indexed \
  lake env lean -DwarningAsError=true tools/compiler-explorer/Replay.lean
make check CHECK_TARGETS=+"$root".StructChecks
```

[coverage]: https://github.com/hiloopai/silmaril-lean/blob/9aeb8467ad1e1f962f9f166965e9fabc4e7e03b4/docs/projects/sqlite-track-e/coverage-v1.md
[release]: ../../../corpus/sqlite/releases.toml#L13-L16
[header]: ../../../corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.h#L149-L153
[manifest]: https://sqlite.org/src/raw/555e07ef33f69a0957d24d8e555b702464a131d6f1607f4c3c1e4551e8e6ca76
[mirror]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/manifest.uuid
[connection]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/sqliteInt.h#L1699-L1706
[db]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/sqliteInt.h#L1511-L1547
[db-grow]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/attach.c#L184-L197
[vdbe]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/vdbeInt.h#L458-L536
[vdbe-link]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/vdbeaux.c#L25-L43
[reprepare]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/prepare.c#L907-L934
[vdbe-cursor]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/vdbe.c#L253-L320
[btcursor]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/btreeInt.h#L531-L559
[cell]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/btreeInt.h#L480-L486
[blob]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/vdbeblob.c#L21-L34
[blob-cursor]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/vdbeblob.c#L75-L108
[blob-reopen]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/vdbeblob.c#L503-L531
[backup]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/backup.c#L21-L42
[backup-init]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/backup.c#L164-L219
[backup-step]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/backup.c#L368-L397
[backup-attach]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/backup.c#L313-L320
[backup-copy]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/backup.c#L747-L783
[vfs]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/sqlite.h.in#L1513-L1546
[registry]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/os.c#L352-L447
[uri]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/main.c#L3268-L3274
[open]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/main.c#L3624-L3645
[attach]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/attach.c#L200-L220
[pager-vfs]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/pager.c#L4994-L5007
[fcntl]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/main.c#L4236-L4249
[sleep]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/main.c#L4195-L4205
[file]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/sqlite.h.in#L743-L765
[os-close]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/os.c#L82-L90
[unix]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/os_unix.c#L257-L275
[inode]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/os_unix.c#L1323-L1334
[memdb]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/memdb.c#L923-L935
[pager]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/pager.c#L619-L705
[pager-layout]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/pager.c#L4923-L4954
[wal]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/wal.c#L511-L535
[pcache]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/pcache.c#L26-L54
[pcache1]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/pcache1.c#L112-L203
[recycle]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/pcache1.c#L903-L938
[pghdr]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/pcache.h#L26-L49
[pghdr-init]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/pcache.c#L501-L544
[mempage]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/btree.c#L2338-L2348
[mmap]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/pager.c#L4124-L4160
[btree]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/btreeInt.h#L345-L460
[sharing]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/btree.c#L2657-L2674
[bt-close]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/btree.c#L2971-L3007
[close-api]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/sqlite.h.in#L319-L357
[close]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/main.c#L1269-L1342
[zombie]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/main.c#L1396-L1439
[backup-count]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/btree.c#L11419-L11426
[finalize]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/vdbeapi.c#L105-L124
[blob-close]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/vdbeblob.c#L360-L376
[blob-abort]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/vdbeblob.c#L454-L463
[internal-finalize]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/vdbeaux.c#L3692-L3703
[backup-finish]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/backup.c#L598-L647
[backup-api]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/sqlite.h.in#L9794-L9817
