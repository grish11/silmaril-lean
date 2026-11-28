module

public import Silmaril.Machine.SQLite.VFS.Defs
public import Silmaril.Machine.SQLite.TrackA.Read.Adapter.Defs
public import Silmaril.Machine.SqliteVfs.PageRead.Release.Defs

@[expose] public section

namespace Silmaril.Machine.SQLite.Pager

open SqliteVfs
open Silmaril.Machine.SqliteVfs.TrackA
open VFS (Opened)

/-- Access already granted by the caller's environment, scoped by path and
generation. This profile has one caller and no lock transition operation. -/
inductive LockLevel where
  | shared
  | exclusive
  deriving DecidableEq, Repr

structure LockGrant where
  file : Opened
  level : LockLevel
  deriving DecidableEq, Repr

def LockGrant.Allows (grant : LockGrant) (opened : Opened) (access : Mode) : Prop :=
  grant.file = opened ∧ (access = .readOnly ∨ grant.level = .exclusive)

/-- A read uses the named backing and the live handle supplied by the open.
A read can use either file mode under an already-held shared or exclusive grant. -/
structure ReadAccess (files : VFS.FileMap) (opened : Opened) (grant : LockGrant)
    (file : FileState) (page : PageRead.Page) : Prop where
  allowed : grant.Allows opened .readOnly
  live : ∃ mode, opened.Live files file mode
  handle : page.handle = opened.handle

/-- Entry to the selected rollback-mode write after transaction setup.
The caller supplies an exclusive grant, live write handles for the two
distinct file roles, and the resident preimage. Journal creation is outside
this boundary. The concrete success/fault theorems start with an empty journal. -/
structure WriteAccess (named : VFS.FileMap) (opened : Opened) (grant : LockGrant) (ctx : Write.Context)
    (files : Write.Files) (cache : PageRead.Cache) (slot : PageRead.SlotId) : Prop where
  allowed : grant.Allows opened .readWrite
  handle : ctx.databaseHandle = opened.handle
  databaseLive : opened.Live named files.database .readWrite
  journalLive : ∃ journal, files.journal = some journal ∧
    journal.mode ctx.journalHandle = some .readWrite
  resident : cache slot = some (.resident ctx.page ctx.oldPage)

/-- Observe the landed write with explicit retirement of the read-cache slot.
Local release rejection yields no write run. Both successful and failed
write runs return the vacant slot. A later admitted read of that slot fetches from backing.
Other slots are outside the write observation. -/
def observeInsert (handler : Semantics.TrackA.Interaction.Coalgebra.Handler Write.vfs Write.Files)
    (files : Write.Files) (cache : PageRead.Cache) (slot : PageRead.SlotId)
    (op : Write.Insert) (vm : Formats.Sqlite.Vdbe.State) (ctx : Write.Context) :
    Except PageRead.Release.ReleaseError (Write.Run × PageRead.Cache) :=
  (PageRead.Release.release cache slot ctx.page).map fun vacant =>
    ((Write.insertAndCommit op vm ctx).run handler files, vacant)

end Silmaril.Machine.SQLite.Pager
