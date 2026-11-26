module

public import Silmaril.Formats.Sqlite.File.WriteProfile.Defs
public import Silmaril.Formats.Sqlite.TableLeaf.Defs
public import Silmaril.Machine.SqliteVfs.PageRead.Defs
public import Silmaril.Semantics.TrackA.Interaction.UB.Defs

/-! One admitted OP_Insert followed by autocommit on an existing ordinary
table leaf. The only journal body in the model is the preimage of that leaf. -/
@[expose] public section

namespace Silmaril.Machine.SqliteVfs.TrackA.Write

open Silmaril.Semantics.TrackA.Interaction
open Silmaril.Formats.Sqlite
open Silmaril.Formats.Sqlite.WriteProfile (Edited Snapshot)

inductive FileId where
  | database
  | journal
  deriving DecidableEq, Repr

/-- The selected write-only extension of the single-file VFS profile. Writes
reuse its requests and replies. Sync is an acknowledgement without a
durability interpretation. Finalization removes the journal file. -/
inductive Call where
  | write (file : FileId) (handle : Handle) (offset : Int) (bytes : Bytes)
  | sync (file : FileId) (handle : Handle)
  | deleteJournal (handle : Handle)
  deriving DecidableEq, Repr

def vfs : Signature := ⟨Call, fun _ => Except SqliteVfs.Error Unit⟩

abbrev Event := vfs.Exchange

structure Files where
  database : FileState
  journal : Option FileState
  deriving DecidableEq, Repr

structure Limits where
  database : Nat
  journal : Nat

/-- Select both the backing and its handle scope by file identity. A sync
fault is injected only after validating the journal handle. A rejected
operation retains the state in this backing. Journal deletion checks only
that the journal exists and the handle has read-write access. -/
def dispatch (limits : Limits) (journalSyncError : Option SqliteVfs.Error := none) :
    Coalgebra.Handler vfs Files :=
  fun files call =>
    match call with
    | .write .database handle offset bytes =>
      let (reply, database) := readWrite limits.database files.database (.write handle offset bytes)
      (reply, { files with database })
    | .write .journal handle offset bytes =>
      match files.journal with
      | none => (.error .invalidHandle, files)
      | some journal =>
        let (reply, journal) := readWrite limits.journal journal (.write handle offset bytes)
        (reply, { files with journal := some journal })
    | .sync .database handle =>
      if files.database.mode handle = some .readWrite then (.ok (), files)
      else (.error .invalidHandle, files)
    | .sync .journal handle =>
      match files.journal with
      | some journal =>
        if journal.mode handle = some .readWrite then
          (journalSyncError.elim (.ok ()) Except.error, files)
        else (.error .invalidHandle, files)
      | none => (.error .invalidHandle, files)
    | .deleteJournal handle =>
      match files.journal with
      | some journal =>
        if journal.mode handle = some .readWrite then (.ok (), { files with journal := none })
        else (.error .invalidHandle, files)
      | none => (.error .invalidHandle, files)

/-- The selected cursor already has its write transaction and points at the
ordinary root leaf on page 2. The old bytes are resident in the Pager. -/
structure Context where
  cursor : Nat
  snapshot : Snapshot
  oldPage : Bytes
  databaseHandle : Handle
  journalHandle : Handle

def Context.page (ctx : Context) : PageRead.Page :=
  ⟨ctx.databaseHandle, 2, Silmaril.Formats.Sqlite.File.Write.pageSize⟩

def openWritable (handle : Handle) (bytes : Bytes) : FileState :=
  ⟨bytes, some .readWrite, handle.generation⟩

/-- Boundary state for the selected backing. The journal starts empty and open.
The database is the canonical two-page image with the resident leaf at page 2. -/
def initialFiles (ctx : Context) (catalogue : Bytes) : Files :=
  ⟨openWritable ctx.databaseHandle (catalogue ++ ctx.oldPage),
   some (openWritable ctx.journalHandle [])⟩

/-- Register operands of the selected form of OP_Insert. P2 contains the
packed record and P3 the integer rowid. -/
structure Insert where
  cursor : Nat
  recordRegister : Nat
  rowidRegister : Nat

inductive Stage where
  | journalOldPage
  | syncJournal
  | writeDatabase
  | syncDatabase
  | deleteJournal
  deriving DecidableEq, Repr

inductive Failure where
  | vmState
  | operands
  | edit (reason : WriteProfile.Error)
  | leaf (reason : Silmaril.Formats.Sqlite.BTree.LeafWrite.Error)
  | vfs (stage : Stage) (reason : SqliteVfs.Error)
  deriving DecidableEq, Repr

structure Success where
  vm : Vdbe.State
  snapshot : Snapshot
  changed : Nat

abbrev Result := Except Failure Success

/-- This finite presentation of the selected interaction uses tau for local
VM and cache steps. Its result embeds into Track A's explicit UB boundary as
an ordinary return, including when it carries a VFS error. -/
inductive Program where
  | done (result : Result)
  | silent (next : Program)
  | call (request : Call) (next : vfs.Response request → Program)

def unfoldProgram : Coalgebra vfs Signature.noChoice (Option Result) Program
  | .done result => .ret (some result)
  | .silent next => .tau next
  | .call request next => .vis request next

structure Run where
  result : Result
  files : Files
  events : List Event

def Program.run (handler : Coalgebra.Handler vfs Files) (files : Files) : Program → Run
  | .done result => ⟨result, files, []⟩
  | .silent next => next.run handler files
  | .call request next =>
    let (reply, after) := handler files request
    let rest := (next reply).run handler after
    { rest with events := ⟨request, reply⟩ :: rest.events }

def issue (stage : Stage) (request : Call) (next : Program) : Program :=
  .call request fun
    | .ok () => next
    | .error reason => .done (.error (.vfs stage reason))

namespace Pager

/-- Context passed to the successful write-admission continuation. The
public constructor carries no evidence of the journal write. -/
structure Writable where
  context : Context

/-- Replacement bytes and their write context, supplied by the caller of
`phaseOne`. -/
structure Dirty where
  page : Writable
  bytes : Bytes

/-- Context passed to the successful phase-one continuation. Callers can
construct this value directly from a `Context`. It carries no I/O history. -/
structure CommitReady where
  context : Context

/-- Record the resident preimage and continue with a `Writable` value
after a successful reply. -/
def admit (ctx : Context) (next : Writable → Program) : Program :=
  issue .journalOldPage (.write .journal ctx.journalHandle 0 ctx.oldPage) (next ⟨ctx⟩)

/-- Sync the journal, write the supplied dirty page, and sync the database.
Callers composing this stage directly are responsible for write admission. -/
def phaseOne (dirty : Dirty) (next : CommitReady → Program) : Program :=
  let ctx := dirty.page.context
  issue .syncJournal (.sync .journal ctx.journalHandle) <|
    issue .writeDatabase (.write .database ctx.page.handle ctx.page.offset dirty.bytes) <|
      issue .syncDatabase (.sync .database ctx.databaseHandle) (next ⟨ctx⟩)

/-- Request journal deletion using the supplied context. Callers composing
this stage directly are responsible for prior completion of phase one. -/
def phaseTwo (ready : CommitReady) (next : Program) : Program :=
  issue .deleteJournal (.deleteJournal ready.context.journalHandle) next

end Pager

/-- Preflight uses the existing logical insert and packed-leaf encoder to
admit fresh rowids that fit without a split. Preparing these bytes is pure.
Installing the dirty cache page follows write admission. -/
def prepareLeaf (ctx : Context) (id amount : Int64) : Except Failure (Edited × Bytes) := do
  let edited ← (ctx.snapshot.apply (.insert (.integer id) (.integer amount))).mapError .edit
  let bytes ← (WriteProfile.Image.tablePage edited.snapshot).mapError .leaf
  pure (edited, bytes)

def btreeInsert (ctx : Context) (id amount : Int64) (next : Edited → Pager.Dirty → Program) :
    Program :=
  match prepareLeaf ctx id amount with
  | .error reason => .done (.error reason)
  | .ok (edited, bytes) =>
    Pager.admit ctx fun writable => .silent (next edited ⟨writable, bytes⟩)

def Insert.operands (op : Insert) (vm : Vdbe.State) (ctx : Context) :
    Except Failure (Int64 × Int64) := do
  if vm.halted.isSome || op.cursor != ctx.cursor then throw .vmState
  let .integer id := vm.registers op.rowidRegister | throw .operands
  let .blob record := vm.registers op.recordRegister | throw .operands
  let some fields := Record.decode? .utf8 record | throw .operands
  let [.null, .integer amount] := fields.toList | throw .operands
  pure (id, amount)

/-- Selected VM entry point. Its continuations sequence write admission and
both commit phases. The successful Halt after the Insert advances the PC
once and sets the existing VDBE halted field. -/
def insertAndCommit (op : Insert) (vm : Vdbe.State) (ctx : Context) : Program :=
  match op.operands vm ctx with
  | .error reason => .done (.error reason)
  | .ok (id, amount) => .silent <|
    btreeInsert ctx id amount fun edited dirty =>
      Pager.phaseOne dirty fun ready =>
        Pager.phaseTwo ready (.done (.ok ⟨{ vm.advance with halted := some 0 },
          edited.snapshot, edited.changed⟩))

/-- Independent flattened request specification of the selected Pager path.
An ordinary failure stops this schedule at the failed request. -/
def schedule (ctx : Context) (newPage : Bytes) : List Call :=
  [.write .journal ctx.journalHandle 0 ctx.oldPage, .sync .journal ctx.journalHandle,
   .write .database ctx.databaseHandle 512 newPage, .sync .database ctx.databaseHandle,
   .deleteJournal ctx.journalHandle]

def completed (ctx : Context) (newPage : Bytes) : List Event :=
  (schedule ctx newPage).map fun call => ⟨call, .ok ()⟩

/-- The flat specification follows successful replies until the schedule is
exhausted, or stops on the first error with that call's actual poststate. -/
inductive FollowsSchedule (handler : Coalgebra.Handler vfs Files) :
    List Call → Files → List Event → Except SqliteVfs.Error Unit → Files → Prop where
  | done (files : Files) : FollowsSchedule handler [] files [] (.ok ()) files
  | next {call : Call} {calls : List Call} {before after finish : Files}
      {events : List Event} {status : Except SqliteVfs.Error Unit} :
      handler before call = (.ok (), after) →
      FollowsSchedule handler calls after events status finish →
      FollowsSchedule handler (call :: calls) before (⟨call, .ok ()⟩ :: events) status finish
  | failed {call : Call} {calls : List Call} {before after : Files} {reason : SqliteVfs.Error} :
      handler before call = (.error reason, after) →
      FollowsSchedule handler (call :: calls) before [⟨call, .error reason⟩] (.error reason) after

/-- Local VM and leaf rejections have no VFS status. A selected execution
that reaches VFS returns either success or an ordinary VFS error. -/
def Result.vfsStatus : Result → Option (Except SqliteVfs.Error Unit)
  | .ok _ => some (.ok ())
  | .error (.vfs _ reason) => some (.error reason)
  | .error _ => none

end Silmaril.Machine.SqliteVfs.TrackA.Write
