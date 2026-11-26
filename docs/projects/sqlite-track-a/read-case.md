# SQLite Track A rowid read

The case models one integer `SeekRowid` on the designated root page of
database zero, starting with an open handle. The six-instruction program
opens the modeled cursor, loads the key, seeks, projects the second column
on a match, emits the row, and halts. The source evidence is SQLite 3.54.1's
`OP_SeekRowid` → `sqlite3BtreeTableMoveto` → `sqlite3PagerGet` → `xRead` cut
in PR #3531, pinned at `627432c060169951a08c2454b1c524831ce48793`. The SQLite
source revision cited there is `57520227c95396ce39ba6ecaac8d475b78dd3964`.
[Pinned operation inventory](https://github.com/hiloopai/silmaril-lean/blob/627432c060169951a08c2454b1c524831ce48793/docs/projects/sqlite-track-a/header-inventory/operations.md)

## Checked interface

Import `Silmaril.Machine.SQLite.TrackA.Read.Thms`. `runStaged` acquires a
page and uses `seekLeaf` to decode it and call `ReadModel.get`. `runComposed`
executes the VDBE program through `runLeaf` and the landed one-leaf adapter.
Both carry the Pager's actual file and cache poststates and completed
request-indexed `SqliteVfs.Exchange`s. `Result` keeps an acquisition,
leaf-decode, or VM failure separate from a completed search. `.ok none`
is absence and `.ok (some value)` is a match. The VM halt status is local to
the model and has no asserted mapping to a SQLite C status code or its
B-Tree comparison out parameter.
[Definitions](../../../Silmaril/Machine/SQLite/TrackA/Read/Defs.lean)

- `program_lookup` applies to any `Vdbe.Table` with its built-in
  `ReadModel.get_eq` law and any `Int64` key. It checks a successful halt
  with zero or one projected row. `runLeaf_lookup` requires that the page
  view decode to the given table at the physical B-Tree header offset.
- `seekLeaf_eq_runLeaf` covers every view, page number, and key, including
  leaf rejection. `staged_eq_composed` equates the full outcomes for any
  supplied handler and starting file/cache. `composed_trace` validates the
  recorded exchanges against that same handler and file transition.
- `readOnly_cold_warm_lookup` assumes equality of the file bytes and the
  image snapshot, `image.page? number = some view`, a live handle, the
  `ReadRange` for `(number - 1) * pageSize` and `pageSize`, an owned vacant
  slot, and successful decoding of the view to the stated table. Cold
  acquisition installs the complete bytes and records exactly the successful
  page read. The warm run starts with that returned file and cache, gives
  the same logical lookup and poststates, and records no exchanges. The
  theorem validates the concatenated trace.
[Public theorem statements](../../../Silmaril/Machine/SQLite/TrackA/Read/Thms.lean)

## Model limits

Leaf admission comes from the existing 512-byte packed rowid-leaf decoder
and its local two-field record profile. Root designation is supplied. The
observation starts at target-page acquisition and excludes transaction
setup and its locks, header reads, or file-version checks. The model has
no C or native simulation, multi-page traversal, mmap, WAL, or SQL-level
correctness claim. A reported I/O failure or short read is an ordinary
modeled failure with its completed VFS exchange. `PageRead.fill` rejects
short reads even though the pinned C main-file branch can accept a
zero-filled buffer and proceed to page-format admission. The comparison
with the source path concerns complete reads.
[Page acquisition contract](../sqlite-page-read.md) · [Leaf adapter](../sqlite-vfs-vdbe-leaf.md)

A separate interaction adapter can use `Request` and `Response` as the VFS
signature and `PageRead.Acquire.acquire` as the Pager handler. Its VM
continuation can pass the returned acquisition to `finishAcquire` with
`runLeaf` or `seekLeaf`. This read case builds directly on `main` and the
adapter can follow the interaction interface in PR #3543, inspected at
`61d4a44f4514730e0779c4180a768abc21086ed7`.
[Dependent interaction core](https://github.com/hiloopai/silmaril-lean/blob/61d4a44f4514730e0779c4180a768abc21086ed7/Silmaril/Semantics/TrackA/Interaction/Defs.lean)

## Reproduction

The executable fixtures encode a 512-byte-page image with rowid 42 and
value 7 through the repository's writer. They check the found key, absent
key 41, cold and warm VFS exchanges, and a truncated backing file. The
kernel replay rechecks the named modules over their imported `.olean`s.
[Fixtures and axiom audit](../../../Silmaril/Machine/SQLite/TrackA/Read/Checks.lean)

```sh
lake build --wfail +Silmaril.Machine.SQLite.TrackA.Read.Checks
make check CHECK_TARGETS=+Silmaril.Machine.SQLite.TrackA.Read.Checks
for module in Silmaril.Proofs.Machine.SQLite.TrackA.Read.Correctness \
    Silmaril.Machine.SQLite.TrackA.Read.Thms; do
  SILMARIL_REPLAY_MODULE="$module" lake env lean -DwarningAsError=true \
    tools/compiler-explorer/Replay.lean || exit 1
done
```
