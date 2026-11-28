# SQLite 3.54.1 C interface inventory

This inventory defines the source and extraction procedure for Track A. It covers
the interfaces needed to follow an ordinary rowid lookup and a single-file
insert from the public C API to the VFS. The companion page records the
branch conditions, alternative paths, and candidate dependent interfaces.
[SQLite architecture](https://sqlite.org/arch.html) · [Operation paths and proof interfaces](operations.md)

## Source and build identity

| Artifact | Identity and provenance |
| --- | --- |
| SQLite 3.54.1 | `SQLITE_VERSION_NUMBER = 3054001`. `SQLITE_SOURCE_ID = "2026-10-16 14:45:20 555e07ef33f69a0957d24d8e555b702464a131d6f1607f4c3c1e4551e8e6ca76"`. [Vendored header at the corpus import][amalg-header] |
| Upstream amalgamation | `sqlite-amalgamation-3540100.zip`, SHA-256 `0a9c8e34352dad46006aa82836d5383bff9dc6bc9ce5a60553c05aa30e6ad1f9`. The archive's `sqlite3.h`, `sqlite3.c`, and `shell.c` match the vendored files byte for byte. [Archive][archive] · [Release manifest](../../../../corpus/sqlite/releases.toml) · [Vendored hashes](../../../../corpus/sqlite/upstream.sha256) |
| Split source | SQLite's GitHub mirror commit `57520227c95396ce39ba6ecaac8d475b78dd3964` is the `version-3.54.1` tag target. Its `manifest.uuid` matches the hash in `SQLITE_SOURCE_ID`. Split-source links below use that mirror commit. [Commit][mirror] · [Fossil identity in mirror][uuid] |
| Corpus default configuration | The corpus compiles the amalgamation directly on Linux with `SQLITE_THREADSAFE=1` and defaults otherwise. The canonical objects use `-O2`. The shared object has soname `libsqlite3.so.0`. The CLI compiles from `shell.c` and dynamically links that library. [Package recipe](../../../../corpus/sqlite/package.toml) · [Build script](../../../../corpus/sqlite/build.sh) |

The architecture diagram describes responsibilities. In the corpus library, the
VM, B-Tree, Pager, WAL and OS dispatch are compiled together in `sqlite3.c`.
The split-source headers provide source-level interfaces within that library.
In the amalgamation `SQLITE_PRIVATE` defaults to `static` and marks internal
declarations such as `sqlite3PagerGet`. A build may inline or eliminate those
calls. The host API and VFS callback tables are external interfaces, while calls
through a VFS table resolve to the implementation selected at runtime.
[Architecture page][arch] · [Amalgamation linkage][amalg-private] · [Pager declaration in the amalgamation][amalg-pager] · [OS dispatch][os-dispatch]

In the canonical x86-64 ELF pair, `readelf -d` reports `libsqlite3.so.0` as
both the library soname and a dependency of the shell. `nm -D --defined-only`
on the library shows `sqlite3_prepare_v2` and `sqlite3_step` among the dynamic
exports. The selected internal symbols `sqlite3VdbeExec`,
`sqlite3BtreeTableMoveto`, `sqlite3PagerGet` and `sqlite3OsRead` are absent
from that table.
[Corpus library](../../../../corpus/elf/sqlite/x86_64/libsqlite3.so) · [Corpus shell](../../../../corpus/elf/sqlite/x86_64/sqlite3)

Record compile-time options and runtime settings independently. Compile-time
selectors include `SQLITE_THREADSAFE`, `SQLITE_OMIT_WAL`,
`SQLITE_OMIT_SHARED_CACHE`, `SQLITE_MAX_MMAP_SIZE` and the platform OS
selection. The corpus `small` configuration sets `SQLITE_THREADSAFE=0`,
`SQLITE_OMIT_LOAD_EXTENSION` and `SQLITE_DEFAULT_MEMSTATUS=0`. Its
`fts5-rtree` configuration enables `SQLITE_ENABLE_FTS5` and
`SQLITE_ENABLE_RTREE` in addition to `SQLITE_THREADSAFE=1`. Runtime selectors
include VFS name and open flags, threading mode, journal and locking modes,
synchronous level, mmap limit, page size, and registered methods.
[Corpus build branches](../../../../corpus/sqlite/build.sh) · [Threading configuration][config] · [Pager acquisition dispatch][pager-getters]

## Declaration extraction and contract review

1. **Pin the inputs.** Record the SQLite source ID, upstream archive and file
   hashes, compiler version, target triple, sysroot or system headers,
   language mode and all defines and include paths. Record the actual build
   flags and runtime choices for any later execution claim. Leave the original
   sources available for line references.
2. **Extract two views.** Include the generated `sqlite3.h` in a C
   translation unit for the public declarations. Use the amalgamation as a
   separate translation unit for active private declarations, since split
   headers depend on generated headers, typedefs and configuration. Map
   declarations back to the split source using the amalgamation's
   `Begin file` markers and the pinned mirror. Retain preprocessing line
   markers and record relevant inactive guards from the unpreprocessed source.
   The mirror's `main.mk` describes generation of `sqlite3.h` and
   `opcodes.h`. [Generation rules][gen-api] · [Opcode generation rules][gen-op] · [Amalgamation][amalg-source]
3. **Record extractable syntax.** For each declaration, store the source
   revision, path, span, active configuration, symbol or record field, and
   declared and canonical types. Keep typedef and tag identity, record field
   order, qualifiers at each pointer level, linkage and visibility attributes,
   parameter order, variadic markers, and function-pointer prototypes. Record
   macro definitions and relevant values separately from AST nodes, including
   flags, result codes and destructor sentinels. For an ABI claim, obtain target
   record size, alignment and field offsets from the selected compiler and
   check exported symbols on the actual object.
4. **Review behavioral obligations.** For each operation, record required live
   objects, permitted aliasing and overlap, buffer extents, ownership transfer
   and invalidation, required lock or transaction state, callback context and
   reentry rules, and the outputs defined for each return case. Cite the
   public contract or internal implementation branch for each rule. Pointer
   depth gives the shape of an out slot. The contract establishes whether
   that slot is required, whether it is written on error, and who owns any
   resulting object. A `const` pointee can still alias storage that another
   handle can change.

Run the extraction example from the repository root with Clang 19 and Linux
x86-64 system headers. The private declaration query shows the amalgamation
linkage with the default configuration.

```sh
(cd corpus/sqlite && sha256sum -c upstream.sha256)
a="$PWD/corpus/sqlite/upstream/sqlite-amalgamation-3540100"
d=$(mktemp -d)
printf '#include "sqlite3.h"\n' > "$d/public.c"
clang --version
clang --target=x86_64-linux-gnu -std=gnu11 -DSQLITE_THREADSAFE=1 -I "$a" \
  -E -dD "$d/public.c" > "$d/sqlite-public.i"
clang --target=x86_64-linux-gnu -std=gnu11 -DSQLITE_THREADSAFE=1 -I "$a" \
  -fsyntax-only -Xclang -ast-dump=json "$d/public.c" > "$d/sqlite-public.json"
clang --target=x86_64-linux-gnu -std=gnu11 -DSQLITE_THREADSAFE=1 \
  -fsyntax-only -Xclang -ast-dump -Xclang -ast-dump-filter -Xclang sqlite3PagerGet \
  "$a/sqlite3.c" > "$d/sqlite-pager-get.ast"
```

For example, the AST gives `sqlite3_prepare_v2` the type
`int (sqlite3 *, const char *, int, sqlite3_stmt **, const char **)`.
It gives the `sqlite3_io_methods.xRead` field the type
`int (*)(sqlite3_file *, void *, int, sqlite3_int64)`. Qualify fields by
their containing record. Both `sqlite3_vfs` and `sqlite3_module` have an
`xOpen` field with different prototypes. The AST also shows
`sqlite3PagerGet` with static linkage in the amalgamation.
[Prepare declaration][api-prepare] · [I/O method declarations][api-io] · [VFS callbacks][api-vfs] · [Virtual table callbacks][api-module] · [Private Pager declaration][amalg-pager]

For a new release or configuration, rerun both views and compare declaration
rows, macro values, callback table versions, and actual exports. Recheck
the contracts against the corresponding source bodies even for rows with
identical types. The procedure produces compiler evidence for the selected
inputs. Semantic adequacy and any source-to-binary correspondence require
their own evidence.

## Interface inventory

The rows list representative operations for each boundary and the contract
details needed by a later proof.

| Boundary | Extractable declarations | Contract obligations and source evidence |
| --- | --- | --- |
| Connection and error state | `sqlite3` opaque handle, `sqlite3_open_v2`, `sqlite3_close`, `sqlite3_close_v2`, `sqlite3_errcode`, `sqlite3_extended_errcode`, open/result-code macros | An ordinary open failure can still return a connection handle for diagnostics and cleanup. If allocation of the connection fails, the out handle is null. `close` can return `SQLITE_BUSY` and leave the connection live while dependent objects remain. `close_v2` can turn it into an unusable zombie pending cleanup of statements, BLOBs and backups. Preserve primary and extended codes, and which operation produced the error recorded on the connection. [Open contract][api-open] · [Close contract][api-close] · [Error API][api-errors] |
| Statement preparation and execution | `sqlite3_stmt` opaque handle, `sqlite3_prepare_v2(db,zSql,nByte,ppStmt,pzTail)`, `sqlite3_step`, `sqlite3_reset`, `sqlite3_finalize` | For admitted inputs, `ppStmt` is required, and success can produce null on empty/comment-only input. Errors set it to null. Optional `pzTail` writes a pointer into the caller's SQL buffer. The statement returned by v2 retains its own SQL copy and can reprepare. Treat `SQLITE_ROW`, `SQLITE_DONE`, busy and errors as distinct outcomes. Reset can report the prior execution error and retains bindings. Finalize consumes the live statement even when it reports an error from evaluation. [Prepare][api-prepare] · [Step][api-step] · [Finalize and reset][api-finalize] |
| Binding and result views | `sqlite3_bind_blob`, destructor function type and `SQLITE_STATIC` / `SQLITE_TRANSIENT`, `sqlite3_column_blob`, `sqlite3_column_bytes` | Static borrows input until the parameter is rebound or the statement is finalized. Transient copies before returning. A custom destructor can run on bind failure, with exceptions for a null data pointer or negative length in the public contract. A column pointer borrows current-row storage, can be null for SQL NULL, zero-length BLOB or conversion allocation failure, and can be invalidated by conversion, step, reset or finalize. [Binding][api-bind] · [Destructor constants][api-destructors] · [Column results][api-columns] |
| Callbacks and registration | `sqlite3_busy_handler`, `sqlite3_create_function_v2`, `sqlite3_context`, `sqlite3_value`, `sqlite3_exec`, `sqlite3_module` and `sqlite3_create_module_v2` | Track the registered function and context together, plus destruction on replacement, close or failed registration where specified. A busy handler can be skipped to avoid deadlock and must avoid reentry into its invoking connection. An `exec` row callback receives call-scoped result arrays and can abort execution. Its optional error-string output uses `sqlite3_free`. Virtual table methods carry their own module, table and cursor lifetimes. [Busy handler][api-busy] · [SQL functions][api-function] · [Exec][api-exec] · [Virtual table methods][api-module] · [Module registration][api-module-register] |
| VM and compiler | `vdbe.h` declares `Vdbe`, `VdbeOp`, `Mem` and code generation operations. `vdbeInt.h` defines `Vdbe`, `VdbeCursor`, and the execution prototype `sqlite3VdbeExec`. Opcode constants are generated. | `vdbeapi.c` implements the public statement wrapper and dispatches into execution. `VdbeCursor` can hold a `BtCursor *`; its type determines which union arm is valid. Operand meaning is specific to each opcode. Follow `case OP_...` bodies and the generating sites for the selected bytecode. SQL prepare and code generation span multiple files and internal headers, with no standalone public compiler or opcode header. [VM header][vdbe-h] · [VM internals][vdbe-int] · [Public step implementation][vdbe-api] · [SQL prepare][prepare] · [Opcode generation][gen-op] |
| B-Tree | `btree.h` declares `Btree`, `BtCursor`, `sqlite3BtreeBeginTrans`, `sqlite3BtreeCursor`, `sqlite3BtreeTableMoveto`, `BtreePayload`, and `sqlite3BtreeInsert`. Layouts are in `btreeInt.h`. | A per-connection `Btree` may share its `BtShared` and Pager under shared cache. Cursor storage is supplied by the caller. It has a current page, ancestor pages and position that may need restoring after mutation. `TableMoveto` has both a status and a separate signed search result. `MemPage.aData` and Pager data refer to the same bytes, and B-Tree page metadata lives in Pager extra storage. [B-Tree declarations][btree-h] · [Handle and cursor layouts][btree-int] · [Cursor initialization][btree-cursor] · [Page aliasing][btree-pages] · [Table seek][btree-seek] |
| Pager, cache and WAL | `pager.h` declares `Pager`, `Pgno`, `DbPage` (a `PgHdr`), page get/write/unref, busy callback and transaction operations. `pcache.h` exposes `PgHdr`. `wal.h` declares WAL functions under build guards. | Page get requires the applicable reader/transaction state. Acquisition returns a page reference on success. The data and extra pointers borrow storage tied to that page reference. Page 1 and mapped pages have specific release paths. Cache hits, normal reads, mmap, no-content acquisition and WAL lookup require different observations. A write first needs a valid write transaction and the Pager's write admission. [Pager header][pager-h] · [Cache layout][pcache-h] · [WAL header][wal-h] · [Acquire and release][pager-release] · [Write transition][pager-write] |
| VFS and OS | The public header defines `sqlite3_vfs`, `sqlite3_file`, `sqlite3_io_methods`, `sqlite3_vfs_register`, and `sqlite3_file_control`. Private `os.h` declares `sqlite3Os*` adapters and platform constants. | The VFS registration, its context and method tables must remain valid while in use. The core supplies file storage of at least `szOsFile`. On failed `xOpen`, `pMethods` can still require `xClose`; the return code alone does not settle cleanup. Output flags depend on the open outcome. `xRead` short reads require zero filling. Method-table versions and available methods govern shared memory and mapping. File-control opcodes determine the type and lifetime of the `void *` argument; `FILE_POINTER` and `VFS_POINTER` expose aliases. [VFS and file contracts][api-vfs] · [I/O methods][api-io] · [OS header][os-h] · [File-control implementation][file-control] |
| Mutexes, locks and configuration | The public header declares `sqlite3_mutex`, `sqlite3_mutex_methods`, `sqlite3_db_mutex`, `sqlite3_config` and `SQLITE_CONFIG_*`. File lock levels are public constants. `mutex.h` selects internal mutex support. | Model connection mutex ownership, shared-cache table locks, Pager file lock transitions, and WAL shared-memory locks as distinct resources. `sqlite3_db_mutex` refers to the connection's mutex and can return null in nonserialized mode. `sqlite3_config` is opcode-dependent and most operations have initialization-state restrictions. For example, `SQLITE_CONFIG_MUTEX` takes a pointer to a methods table that SQLite copies, and its availability depends on the build. An OS locking proof needs the selected VFS and OS behavior as premises. [Mutex API][api-mutex] · [Configuration][config] · [Configuration arguments][config-args] · [Mutex build selection][mutex-h] · [File locks][file-lock] · [Shared-cache locks][btree-locks] · [WAL locks][wal-lock] |

Some boundaries are defined by implementation rather than by a standalone
header. The Pager state machine and its `xGet` dispatch live in
`pager.c`. The Unix `sqlite3_file` subtype, method table selection, OS lock
operations, and shared-memory lock bookkeeping live in `os_unix.c`. Windows
has its own implementation. The extension loader's public dispatch table is
separate in upstream `sqlite3ext.h`; its indirection is another call path
for extensions. [Pager states][pager-states] · [Unix method tables][unix-table] · [Unix lock implementation][unix-lock] · [Windows lock implementation][win-lock] · [Extension API][ext-header]

[arch]: https://sqlite.org/arch.html
[archive]: https://sqlite.org/2026/sqlite-amalgamation-3540100.zip
[mirror]: https://github.com/sqlite/sqlite/commit/57520227c95396ce39ba6ecaac8d475b78dd3964
[uuid]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/manifest.uuid
[amalg-header]: https://github.com/hiloopai/silmaril-lean/blob/b95e373a65c5e4f70d4a8caf90a6ce77afb768e9/corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.h#L149-L151
[amalg-source]: https://github.com/hiloopai/silmaril-lean/blob/b95e373a65c5e4f70d4a8caf90a6ce77afb768e9/corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L16960-L16966
[amalg-private]: https://github.com/hiloopai/silmaril-lean/blob/b95e373a65c5e4f70d4a8caf90a6ce77afb768e9/corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L1-L31
[amalg-pager]: https://github.com/hiloopai/silmaril-lean/blob/b95e373a65c5e4f70d4a8caf90a6ce77afb768e9/corpus/sqlite/upstream/sqlite-amalgamation-3540100/sqlite3.c#L17119-L17138
[gen-api]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/main.mk#L1140-L1158
[gen-op]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/main.mk#L1459-L1467
[api-open]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/sqlite.h.in#L3750-L4042
[api-close]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/sqlite.h.in#L313-L357
[api-errors]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/sqlite.h.in#L4218-L4320
[api-prepare]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/sqlite.h.in#L4524-L4670
[api-step]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/sqlite.h.in#L5266-L5361
[api-finalize]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/sqlite.h.in#L5642-L5705
[api-bind]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/sqlite.h.in#L4941-L5061
[api-destructors]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/sqlite.h.in#L6465-L6479
[api-columns]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/sqlite.h.in#L5457-L5637
[api-busy]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/sqlite.h.in#L3010-L3068
[api-function]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/sqlite.h.in#L5707-L5864
[api-exec]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/sqlite.h.in#L361-L436
[api-module]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/sqlite.h.in#L7720-L7789
[api-module-register]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/sqlite.h.in#L7985-L8030
[api-vfs]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/sqlite.h.in#L1337-L1536
[api-io]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/sqlite.h.in#L737-L876
[api-mutex]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/sqlite.h.in#L8401-L8666
[config]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/sqlite.h.in#L1695-L1730
[config-args]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/sqlite.h.in#L1997-L2012
[os-dispatch]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/os.c#L88-L112
[os-h]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/os.h
[vdbe-h]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/vdbe.h
[vdbe-int]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/vdbeInt.h
[vdbe-api]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/vdbeapi.c#L910-L1008
[prepare]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/prepare.c#L857-L971
[btree-h]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/btree.h
[btree-int]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/btreeInt.h#L345-L570
[btree-cursor]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/btree.c#L4718-L4835
[btree-pages]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/btree.c#L2338-L2462
[btree-seek]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/btree.c#L5804-L5979
[btree-locks]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/btree.c#L128-L249
[pager-h]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/pager.h
[pager-states]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/pager.c#L145-L315
[pager-getters]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/pager.c#L1035-L1057
[pager-release]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/pager.c#L5788-L5877
[pager-write]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/pager.c#L6112-L6187
[pcache-h]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/pcache.h#L16-L85
[wal-h]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/wal.h
[file-control]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/main.c#L4224-L4280
[mutex-h]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/mutex.h#L24-L65
[file-lock]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/os.h#L94-L155
[wal-lock]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/wal.c#L1111-L1160
[unix-table]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/os_unix.c#L5816-L5859
[unix-lock]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/os_unix.c#L1802-L1985
[win-lock]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/os_win.c#L2342-L2405
[ext-header]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/sqlite3ext.h
