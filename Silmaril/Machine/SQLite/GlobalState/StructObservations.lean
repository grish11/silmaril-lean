module

public import Silmaril.Machine.SQLite.GlobalState.Indexed
public import Silmaril.Machine.SQLite.Pager.Defs

@[expose] public section

namespace Silmaril.Machine.SQLite.GlobalState

open SqliteVfs

/-- The named-file information needed by the existing Pager read profile. -/
structure NamedMainFile where
  opened : VFS.Opened
  mode : Mode
  pageSize : Nat
  deriving DecidableEq, Repr

/-- Follow the Pager's main-file edge. The supplied handle is scoped to the
named backing, and its liveness is checked by the adapter's premise. -/
def IndexedStore.namedMainFile (store : IndexedStore) (id : LocalId .pager)
    (handle : Handle) : Option NamedMainFile := do
  let pager ← store.lookup id
  let file ← store.lookup pager.mainFile
  let path ← file.path
  let mode ← file.openMode
  return ⟨⟨path, handle⟩, mode, pager.pageSize⟩

def NamedMainFile.page (main : NamedMainFile) (number : Nat) : PageRead.Page :=
  ⟨main.opened.handle, number, main.pageSize⟩

/-- A live, read-granted named backing supplies the existing Pager premise. -/
theorem NamedMainFile.readAccess (main : NamedMainFile) (number : Nat)
    {files : VFS.FileMap} {file : FileState} {grant : Pager.LockGrant}
    (live : main.opened.Live files file main.mode)
    (allowed : grant.Allows main.opened .readOnly) :
    Pager.ReadAccess files main.opened grant file (main.page number) :=
  ⟨allowed, ⟨main.mode, live⟩, rfl⟩

end Silmaril.Machine.SQLite.GlobalState
