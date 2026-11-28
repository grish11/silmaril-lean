# SQLite Track A representative write

The model starts after write-transaction setup, with one admitted cursor
on the existing ordinary table root at page 2. It executes the selected
form of `OP_Insert` and the subsequent successful autocommit `Halt`.
The source profile is the single-file rollback DELETE path with
`synchronous=FULL`, an existing leaf, no hot journal, and a new row that
fits in the leaf. The inventory records the selected SQLite source branches
and the corresponding instrumented fixture.
[Source profile and fixture](https://github.com/hiloopai/silmaril-lean/blob/627432c060169951a08c2454b1c524831ce48793/docs/projects/sqlite-track-a/header-inventory/operations.md#insert-and-commit)

## Selected upstream Pager ordering

When `pager_write` enters in `PAGER_WRITER_LOCKED`, it calls
`pager_open_journal` before `sqlite3PcacheMakeDirty`. A journal-open
failure returns before the dirty mark. For the selected existing page
that has yet to be journalled, SQLite marks it dirty, records its old
bytes in the rollback journal, and sets `PGHDR_WRITEABLE` only after that
record succeeds. The fitting-cell path in `insertCellFast` edits the
cached page after `sqlite3PagerWrite` succeeds.
[Pager write admission](https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/pager.c#L6127-L6175) · [B-Tree leaf edit](https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/btree.c#L7496-L7531)

## Composition and backing

1. The VM adapter takes the cursor and P2/P3 operands from the selected
   instruction and the existing `Vdbe.State`. P2 is a blob decoded by the
   SQLite record decoder as a NULL rowid-alias slot and an integer amount.
   P3 is a signed integer rowid. The running VM and selected cursor identity
   are checked.
2. The B-Tree preflights a fresh-key insertion using `Snapshot.apply` and
   serializes the edited snapshot with `Image.tablePage`. The encoder admits
   a packed leaf that fits one 512-byte page. After successful Pager write
   admission, the B-Tree installs those bytes in the modeled dirty page.
3. Pager admission records the old resident bytes in the rollback journal.
   Phase one waits for journal sync, writes the dirty page at database
   offset 512, and waits for database sync. Phase two removes the journal.
   Successful completion advances the original VM's PC once, sets its halt
   code to zero, and returns the edited snapshot and one changed row.
4. The VFS handler routes by database or journal identity before checking
   handles. Both writes use the existing `SqliteVfs.readWrite` backing,
   including its capacity, range, and generation checks. Sync and DELETE
   extend that interface for this profile. The two handles may have equal
   generations because their file identities differ.

[Definitions](../../Silmaril/Machine/SqliteVfs/TrackA/Write/Defs.lean)

## Public Pager stages

`Pager.Writable`, `Pager.Dirty`, and `Pager.CommitReady` have public
constructors. They carry context and page data for the continuations.
Callers composing individual stages are responsible for the preceding
steps. A caller can construct `Pager.CommitReady.mk ctx` and pass it
directly to `Pager.phaseTwo`. Running that stage on
`initialFiles ctx catalogue` with `dispatch` deletes the open journal
in its first exchange. Deletion checks that the handle identifies an
open read-write journal.

The checked ordering comes from the continuations in `insertAndCommit`.
With admitted VM operands and successful leaf preflight,
`run_follows_schedule` requires each preceding call to succeed before
the delete request can be issued.

## Checked statements

- `run_follows_schedule` relates a run of `insertAndCommit` to a separately
  written list of calls. Given successful VM operand decoding and leaf
  preflight, it holds for any stateful handler of the selected VFS
  signature. The flat relation records completed calls and actual replies,
  stops on the first error, and retains the handler's actual poststate.
- `database_write_requires_journal` uses that relation to show that even a
  failed database write attempt in that run follows a successful write of
  the resident preimage and a successful sync on the journal handle.
- `commit_success` assumes successful VM operand decoding, logical insertion
  of the fresh rowid, a resident preimage matching the packed old snapshot,
  the canonical catalogue page, and successful packing of the edited
  snapshot. The initial backing has that catalogue and preimage, an empty
  open journal, and open read-write handles. The fault-free handler needs
  capacity of at least 512 bytes for the journal and 1024 for the database.
  The theorem gives the five successful exchanges, a halted VM with one
  changed row, identical catalogue bytes, the new database leaf, and no
  remaining journal. The actual resulting file bytes reopen to the edited
  read table, and the logical row list is the inserted row followed by all
  old rows.
- `journal_sync_failure` assumes successful operand decoding and leaf
  preflight, the packed old snapshot as resident preimage, and enough journal
  capacity. With a fault injected at journal sync, it gives exactly the
  successful journal write and failed sync exchanges. The old database
  backing and the recorded journal both survive, and the VM returns the
  ordinary error at the sync stage.
- `run_observes` embeds the handler-selected trace and result into Track A's
  typed interaction observations. `no_ub` excludes an explicit UB marker
  from every observation of this finite presentation. An ordinary VFS error
  is a returned value at that boundary.

[Theorem header](../../Silmaril/Machine/SqliteVfs/TrackA/Write/Thms.lean)

## Abstraction limits

The target is the repository's existing canonical two-page integer-table
profile. The source fixture uses a 4096-byte SQLite database. The model
uses the 512-byte packed encoder and rebuilds the leaf in memory. The
initial context supplies the write cursor and resident page. The initial
backing starts with an empty open journal. Model write admission records
the old bytes before the B-Tree installs the replacement in `Pager.Dirty`.
That installation represents the cache edit. SQLite's earlier dirty-list
mark, journal opening and its failure path are outside the model. The
journal write represents only the old page bytes, and the database write
represents only the target leaf. SQLite journal headers, record framing
and checksums, the page-1 change counter, close, and the source's detailed
sync substeps are outside the event alphabet.

Sync acknowledgement expresses ordering in the model. Storage persistence,
crash recovery and rollback after faults, lock upgrades and contention,
spill, splits, allocation, indexes, WAL, and multi-file commit are outside
the checked profile. The fixture identifies source paths to motivate the
model. A relation to C or compiled SQLite execution and an exact source
VFS trace are separate proof obligations.

## Reproduction

```sh
lake build --wfail +Silmaril.Machine.SqliteVfs.TrackA.Write.Thms
lake env leanchecker Silmaril.Machine.SqliteVfs.TrackA.Write.Defs
lake env leanchecker Silmaril.Proofs.Machine.SqliteVfs.TrackA.Write.Correspondence
lake env leanchecker Silmaril.Proofs.Machine.SqliteVfs.TrackA.Write.Backing
lake env leanchecker Silmaril.Machine.SqliteVfs.TrackA.Write.Thms
```
