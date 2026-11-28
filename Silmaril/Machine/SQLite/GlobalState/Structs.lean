module

public import Silmaril.Machine.SQLite.GlobalState.Defs
public import Silmaril.Machine.SqliteVfs.Defs
public import Std.Data.ExtTreeMap.Basic

@[expose] public section

namespace Silmaril.Machine.SQLite.GlobalState

/-- A caller-supplied slot in one kind's identity space. -/
structure LocalId (kind : ObjectKind) where
  slot : Nat
  deriving DecidableEq, Repr

/-- The disjoint sum of the local identity spaces. Equality compares both fields. -/
structure TaggedId where
  kind : ObjectKind
  slot : Nat
  deriving DecidableEq, Repr

instance : Hashable TaggedId where
  hash id := hash id.slot

def LocalId.tagged {kind : ObjectKind} (id : LocalId kind) : TaggedId := ⟨kind, id.slot⟩

def TaggedId.localId (id : TaggedId) : LocalId id.kind := ⟨id.slot⟩

/-- An element of `sqlite3.aDb`. Its position in that array can change. -/
structure BackendSlot (Ref : ObjectKind → Type) where
  schemaName : String
  btree : Option (Ref .btree)

structure ConnectionFields (Ref : ObjectKind → Type) where
  vfs : Option (Ref .vfs)
  firstStatement : Option (Ref .statement)
  backends : List (BackendSlot Ref)

/-- `Vdbe.ppVPrev` names the slot containing the incoming list link. The
connection for `connectionHead` is the statement's own connection. -/
inductive StatementLink (Ref : ObjectKind → Type) where
  | connectionHead
  | predecessorNext (predecessor : Ref .statement)

/-- A cache-local header slot, interpreted through the cursor or B-tree's Pager. -/
structure BufferedPageSlot where
  index : Nat
  deriving DecidableEq, Repr

/-- The B-tree variant of a VDBE cursor slot, with its inline `BtCursor`. -/
structure BtreeCursorFields (Ref : ObjectKind → Type) where
  btree : Ref .btree
  rootPage : Nat
  current : Option BufferedPageSlot
  parents : List BufferedPageSlot

structure StatementFields (Ref : ObjectKind → Type) where
  connection : Ref .connection
  incoming : StatementLink Ref
  next : Option (Ref .statement)
  sql : Option String
  btreeCursors : List (Option (BtreeCursorFields Ref))

/-- A usable blob borrows its private statement's B-tree cursor in slot zero. -/
structure BlobFields (Ref : ObjectKind → Type) where
  connection : Ref .connection
  statement : Option (Ref .statement)
  schemaName : String
  column : Nat
  byteOffset : Nat
  byteCount : Nat

inductive BackupNotification (Ref : ObjectKind → Type) where
  | detached
  | attached (next : Option (Ref .backup))

/-- Public backup objects. The destination B-tree is acquired during step. -/
structure BackupFields (Ref : ObjectKind → Type) where
  sourceConnection : Ref .connection
  sourceBtree : Ref .btree
  destinationConnection : Ref .connection
  destinationSchema : String
  destinationBtree : Option (Ref .btree)
  notification : BackupNotification Ref

/-- Registration order is carried by the kind core's `VfsRoots`. -/
structure VfsFields where
  name : String
  osFileSize : Nat
  maxPathname : Nat

/-- Selected file observations. `openMode = none` allows allocated file
storage whose methods are not installed. -/
structure FileFields where
  path : Option String
  openMode : Option SqliteVfs.Mode

structure DirtyLinks where
  next : Option BufferedPageSlot
  previous : Option BufferedPageSlot

/-- Buffered header and page content. The slot and logical page number are
independent. The lower cache entry and B-tree page view share its storage. -/
structure BufferedPageFields where
  number : Nat
  bytes : SqliteVfs.Bytes
  references : Nat
  dirty : Option DirtyLinks

/-- Selected `PCache` state. Map keys are the cache-local slot indices. -/
structure PageCacheFields where
  pages : Std.ExtTreeMap Nat BufferedPageFields
  dirtyHead : Option BufferedPageSlot
  dirtyTail : Option BufferedPageSlot

structure PagerFields (Ref : ObjectKind → Type) where
  vfs : Ref .vfs
  cache : Ref .pageCache
  mainFile : Ref .file
  journal : Ref .file
  subjournal : Ref .file
  backupHead : Option (Ref .backup)
  pageSize : Nat

/-- A scoped `BtShared` projection for a nonshared backend. -/
structure BtreeContent (Ref : ObjectKind → Type) where
  pager : Ref .pager
  pageOne : Option BufferedPageSlot

structure BtreeFields (Ref : ObjectKind → Type) where
  connection : Ref .connection
  content : BtreeContent Ref
  sourceBackupCount : Nat

/-- The fields carried by the object kind. References classify their target
kind at the type level. Lifetime and referential integrity are separate. -/
def ObjectFields (Ref : ObjectKind → Type) : ObjectKind → Type
  | .connection => ConnectionFields Ref
  | .statement => StatementFields Ref
  | .blob => BlobFields Ref
  | .backup => BackupFields Ref
  | .vfs => VfsFields
  | .file => FileFields
  | .pageCache => PageCacheFields
  | .pager => PagerFields Ref
  | .btree => BtreeFields Ref

/-- The instance used by the slot-based indexed store. -/
abbrev LocalFields := ObjectFields LocalId

end Silmaril.Machine.SQLite.GlobalState
