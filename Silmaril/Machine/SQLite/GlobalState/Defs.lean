module

public import Std.Data.ExtHashMap.Basic

@[expose] public section

namespace Silmaril.Machine.SQLite.GlobalState

universe u

/-- Object classes represented by the kind-only store. -/
inductive ObjectKind where
  | connection
  | statement
  | blob
  | backup
  | vfs
  | file
  | pageCache
  | pager
  | btree
  deriving DecidableEq, Repr

/-- A finite partial map from caller-supplied abstract identities to kinds. -/
def ObjectStore (ObjectId : Type u) [BEq ObjectId] [Hashable ObjectId] :=
  Std.ExtHashMap ObjectId ObjectKind

namespace ObjectStore

variable {ObjectId : Type u} [BEq ObjectId] [Hashable ObjectId]

def empty : ObjectStore ObjectId := (∅ : Std.ExtHashMap ObjectId ObjectKind)

variable [LawfulBEq ObjectId]

def lookup (store : ObjectStore ObjectId) (id : ObjectId) : Option ObjectKind :=
  Std.ExtHashMap.get? store id

/-- Replace the kind at this identity, adding a binding if necessary. -/
def insert (store : ObjectStore ObjectId) (id : ObjectId)
    (kind : ObjectKind) : ObjectStore ObjectId :=
  Std.ExtHashMap.insert store id kind

def erase (store : ObjectStore ObjectId) (id : ObjectId) :
    ObjectStore ObjectId :=
  Std.ExtHashMap.erase store id

def HasKind (store : ObjectStore ObjectId) (id : ObjectId) (kind : ObjectKind) : Prop :=
  store.lookup id = some kind

/-- An identity whose kind is known in this store snapshot. -/
abbrev Ref (store : ObjectStore ObjectId) (kind : ObjectKind) :=
  {id : ObjectId // store.HasKind id kind}

end ObjectStore

end Silmaril.Machine.SQLite.GlobalState
